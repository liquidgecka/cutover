#!/usr/bin/python

# A simple process manager that manages port redirection when a new process
# starts.
#
# This system requires the use of Linux (for cgroup and iptables support)
# and several python packages that available on ubuntu as:
#  python-inotifyx, python-netfilter
#
# This will manage process starts and stops for a given service. It will start
# a new one and then seamlessly switch traffic to it when it becomes ready,
# eventually signaling the old process to cleanly shut down.
#
# It is also safe to restart the manager process. It will not kill its children
# when it exits, which in turn allows it to be restarted with new
# configuration cleanly. Its state is fully managed by the kernel. Note that
# when the manager restarts it will automatically trigger a deploy, even if it
# is to the same version.
#
# There is also an optional mode where it will watch a symlink for updates
# which in turn will trigger an automatic deploy.

from __future__ import print_function

import argparse
import grp
import logging
import os
import pwd
import random
import re
import signal
import socket
import subprocess
import sys
import time

from netfilter.rule import Match
from netfilter.rule import Rule
from netfilter.rule import Target
from netfilter.table import Table

log = logging.getLogger('manager')
ch = logging.StreamHandler(sys.stdout)
formatter = logging.Formatter(
        '%(asctime)s - %(name)s - %(levelname)s - %(message)s')
ch.setFormatter(formatter)
log.addHandler(ch)
log.setLevel(logging.INFO)

parser = argparse.ArgumentParser(description='Process manager.')
parser.add_argument('--port', metavar='PORT', type=int, required=True,
        help='The static port.')
parser.add_argument('--http_pool', metavar='PORT-POOL', type=str, required=True,
        help='The range of ports that will be used as dynamic ports for http.')
parser.add_argument('--cgroup', metavar='CGROUP', type=str, required=True,
        help='The cgroup that all processes belong too.')
parser.add_argument('--user', metavar='USERNAME', type=str, required=False,
        help='The user to run the child process as.')
parser.add_argument('--group', metavar='GROUP', type=str, required=False,
        help='The group to run the process as.')
parser.add_argument('--warm_up', metavar='SECS', type=int, required=False,
        default=0.0,
        help='Number of seconds to wait after a succesful healthcheck before '
             'considering the process ready.')
parser.add_argument('--check_http_path', metavar='PATH', type=str,
        required=False, default=None,
        help='The path to expect a 200 response from. This enables http '
             'health checks.')
parser.add_argument('--check_tcp_port', default=False, action='store_true',
        help='Health check by opening a tcp connection only.')
parser.add_argument('--health_check_interval', type=float, required=False,
        default=1.0,
        help='Seconds to wait between normal state health checks.')
parser.add_argument('--failed_health_check_interval', type=float,
        required=False, default=0.1,
        help='After the first failure health check this quickly.')
parser.add_argument('--max_health_check_failures', type=int, required=False,
        default=3,
        help='The number of consecutive health check failures to allow before '
             'forcing a process restart.')
parser.add_argument('--watch_symlink', metavar='SYMLINK', type=str,
        required=False, default='',
        help='Symlink to watch in order to trigger an automatic deploy.')
parser.add_argument('command', metavar='SHELL_COMMAND', type=str,
        help='The shell command to be run to start a new process.')
args = parser.parse_args()

def port(arg, value):
    """Returns a valid port or terminates with an error."""
    if value < 1 or value > 65535:
        log.critical('Invalid port for %s: "%s", Should be a number between 1 and 65535.', arg, value)
        sys.exit(1)
    return value

def port_range(arg, value):
    """Returns a valid port range tuple or terminates with an error."""
    parts = value.split('-')
    if len(parts) != 2:
        log.critical('Invalid argument for %s: "%s", should be PORT-PORT', arg, value)
        sys.exit(1)
    try:
        ports = (int(parts[0]), int(parts[1]))
    except ValueError as e:
        log.critical('Invalid argument for %s: "%s", ports should be integers', arg, value)
        sys.exit(1)
    for port in ports:
        if port < 1 or port > 65535:
             log.critical('Invalid port for %s: "%s", ports should be between 1 and 65535.', arg, port)
             sys.exit(1)
    if ports[0] > ports[1]:
         log.critical('The second port must be larger for {0}: "{1}"',
                 arg, value)
         sys.exit(1)
    return ports

# Make sure all the aguments are defined and proper.
port = port('--port', args.port)
http_pool = port_range('--http_pool', args.http_pool)

command = args.command
user = args.user
group = args.group
cgroup = args.cgroup
warm_up = args.warm_up
watch_symlink = args.watch_symlink
health_check_interval = args.health_check_interval
failed_health_check_interval = args.failed_health_check_interval
max_health_check_failures = args.max_health_check_failures
args = None

start_deploy = False
deployed_symlink_value = ''

# Reads the watch_symlink value and returns the contents.
def read_symlink():
    try:
        return os.readlink(watch_symlink)
    except IOError:
        return ''

def signal_handler(sig, frame):
    """Called on SIGHUP or SIGCHLD"""
    global start_deploy
    if sig == signal.SIGHUP:
         start_deploy = True

signal.signal(signal.SIGHUP, signal_handler)
signal.signal(signal.SIGCHLD, signal_handler)

def cgroup_processes():
    """Returns a list of all existing processes in the cgroup."""
    with open('/sys/fs/cgroup/cpu/{0}/tasks'.format(cgroup), 'r') as fd:
        tasks = set((x.strip() for x in fd.readlines()))
    # Since the above is all tasks, which includes threads, we need to
    # search /proc to see which of the above tasks are actually
    # full processes on the system.
    processes = set(os.listdir('/proc')).intersection(tasks)

    # Lastly we remove our own process so that we don't kill ourselves.
    processes.remove(str(os.getpid()))

    # Return the remaining set as integers, and sorted.
    return sorted((int(x) for x in processes))

def all_used_ports():
    """Returns a list of all used port numbers on the system."""
    used_ports = set()
    with open('/proc/net/tcp', 'r') as fd:
        for line in fd.readlines():
            elm = [e for e in line.split(' ') if e]
            if len(elm) < 2 or elm[1] == 'local_address':
                continue
            parts = elm[1].split(':')
            if len(parts) != 2:
                continue
            used_ports.add(int(parts[1], 16))
    with open('/proc/net/tcp6', 'r') as fd:
        for line in fd.readlines():
            elm = [e for e in line.split(' ') if e]
            if len(elm) < 2 or elm[1] == 'local_address':
                continue
            parts = elm[1].split(':')
            if len(parts) != 2:
                continue
            used_ports.add(int(parts[1], 16))
    return sorted(used_ports)

def find_free_ports(port_pool):
    """Returns a pair of free ports for use with a new process."""
    free = set(xrange(*port_pool)).difference(all_used_ports())
    if len(free) < 1:
        log.error('Unable to find free ports to start a new process.')
        return None, None
    free = list(free)
    random.shuffle(free)
    return free[0]

def outbound_network_interface():
    """Returns the default outbound network interface."""
    devices = sorted(os.listdir('/sys/class/net'))
    if 'lo' in devices:
        devices.remove('lo')
    return devices.pop()

def start_new_process(port):
    """Starts a new command in the background."""
    def dropprivs():
        """Drops to the right user, sets the pgroup, etc."""
        if group:
            os.setgid(grp.getgrnam(group).gr_gid)
        if user:
            os.setuid(pwd.getpwnam(user).pw_uid)
        os.setpgrp()
    env = os.environ.copy()
    env['PORT'] = str(port)
    p = subprocess.Popen(
            command, shell=True, close_fds=True, cwd='/', env=env,
            preexec_fn=dropprivs, stdout=sys.stderr)
    return p.pid

def tcp_healthcheck(port):
    """Performs a simple TCP health check against the port."""
    s = socket.socket()
    try:
        s.connect(('127.0.0.1', port))
    except socket.error as e:
        log.info('Health check error: %s', e)
        s.close()
        return False
    s.close()
    return True

def http_healthcheck(port):
    """Performs a health check against the given port, returns True/False."""
    import httplib
    import urllib2
    try:
        u = urllib2.urlopen('http://127.0.0.1:{0}/{1}'.format(
            port, args.check_http_path))
        u.close()
        return u.getcode() == 200
    except urllib2.URLError as e:
        log.info('Healthcheck error: %s', e)
        return False
    except urllib2.HTTPError as e:
        log.info('Healthcheck error: %s', e)
        return False
    except httplib.HTTPException as e:
        log.info('Healthcheck error: %s', e)
        return False
    except socket.error as e:
        log.info('Healthcheck error: %s', e)
        return False

def healthcheck(port):
    """Calls either tcp or http health check."""
    if args.check_http_path:
        return http_healthcheck(port)
    elif args.check_tcp_port:
        return tcp_healthcheck(port)
    else:
        return True

def replace_redirect(port, port_real):
    """Sets up an iptables rule to redirect traffic."""
    table = Table('nat')

    def add_rule(chain, source, to):
        """Adds a rule to the given table."""
        rule = Rule(protocol='tcp')
        if chain == 'PREROUTING':
            interface = outbound_network_interface()
            rule.in_interface = interface
        else:
            rule.out_interface = 'lo'
            interface = 'lo'
        rule.matches = [Match('tcp', '--dport {0}'.format(source))]
        rule.jump = Target('REDIRECT', '--to-port {0}'.format(to))
        table.prepend_rule(chain, rule)
        log.debug('Added a redirect for %s to %s on %s.', source, to, interface)

    def clean_chain(chain, port_pairs):
        """Removes all but the first rules matching the given port pairs."""
        for rule in table.list_rules(chain):
            log.debug('Processing rule: %s', rule)
            if rule.protocol != 'tcp':
                log.debug('Skipping.. its not a tcp rule.')
                continue
            for match in rule.matches:
                dport = match.options().get('dport', [None])[0]
                if dport != str(port_real):
                    log.debug('Rule is not for a port we care about: %s', dport)
                    continue
                if not rule.jump:
                    log.debug('Rule has no target defined.')
                    continue
                jump_port = rule.jump.options().get('to-ports', [None])[0]
                pair = (int(dport), int(jump_port))
                if pair in port_pairs:
                    log.debug('Keeping the first instance of the pair: %s', pair)
                    port_pairs.remove(pair)
                    continue
                log.debug('Removing the rule.')
                table.delete_rule(chain, rule)

    # Redirect rules
    add_rule('PREROUTING', port_real, port)
    add_rule('OUTPUT', port_real, port)

    # Generate a list of port pairs we want to keep through the chains.
    port_pairs=[(port_real, port)]
    clean_chain('PREROUTING', set(port_pairs))
    clean_chain('OUTPUT', set(port_pairs))

    # Success
    log.debug('Done setting up iptables.')

def wait_for_children():
    """Waits for all children that have actually terminated."""
    i = 0
    while True:
        try:
            # Non-blocking wait (WNOHANG) which returns either a pid if it
            # reaps a child, 0 if no children are zombies, or OSError if there
            # are not children running at all.
            pid, _, _ = os.wait3(os.WNOHANG)
            if pid == 0:
                break
            i += 1
        except OSError:
            break
    if i == 1:
        log.debug('Reaped 1 child.')
    elif i > 1:
        log.debug('Reaped %d children.', i)
    return

def deploy():
    """Deploys a new process seamlessly."""
    # Signal that the deploy work flow has started. We need this to ensure that
    # we can tell if another SIGHUP has been received.
    global start_deploy
    start_deploy = False

    # Let the user know whats up.
    log.info('Starting a deploy.')

    # Get a list of all old processes that we will need to kill once the new
    # task is serving requests.
    existing_processes = cgroup_processes()
    log.debug('%d existing processes', len(existing_processes))

    # Get the ports fot the new task, and start it in the background.
    new_port = find_free_ports(http_pool)
    if new_port is None:
        log.error('Unable to start a new instance, there are no free ports.')
        return

    # Actually start the new process.
    pid = start_new_process(new_port)
    log.info('Started a new task with pid=%s, port=%s',
            pid, new_port)

    # Wait for one of 3 conditions:
    #  1) The health check succeeds on the new port.
    #  2) The process takes too long to become healthy and the current
    #     process is still reporting healthy.
    #  3) Another deploy is signaled.
    #  4) The child process died during the deploy.

    # Timeout this deploy after 5 minutes.
    timeout = time.time() + 300
    warmup_deadline = None

    while True:
        # Condition 1, new deploy.
        if start_deploy:
            log.warning('Deploy aborted due to a new deploy being triggered.')
            try:
                os.kill(pid, signal.SIGTERM)
            except OSError:
                pass
            return

        # Condition 2: new proc is healthy
        if healthcheck(new_port):
            # no warm up, so activate the new proc
            if warm_up == 0:
                break
            # start the warm up period
            if warmup_deadline is None:
                log.debug("Starting the warmup period")
                warmup_deadline = time.time() + warm_up
            # warm up finished, activate the new proc
            if time.time() > warmup_deadline:
                log.debug("Warmup period complete.")
                break
            # fall through and wait, because we are still warming up.
        else:
            # Any time the process fails a health check we have to reset the
            # warmup timer.
            warmup_deadline = None

        # Condition 3, timeout. if the original process still lives
        # (port is still pointing to original) then kill the newer,
        # timed-out process.
        if time.time() > timeout:
            log.error('Deploy timed out, aborting the new process.')
            try:
                os.kill(pid, signal.SIGTERM)
            except OSError:
                pass
            return

        # Condition 4: the child died.
        if pid not in cgroup_processes():
            log.warning('The new process died. Aborting the deploy.')
            return

        # No conditions met, clear any children, then wait 1 second. This
        # time.sleep will be interrupted by any signal that gets sent to this
        # process. So if the child dies then we will find out without
        # delay.
        wait_for_children()
        time.sleep(1)
        log.debug('Looping waiting for a new process.')

    # Success condition. Change iptables.
    log.info('Redirecting traffic.')
    replace_redirect(new_port, port)

    # Kill all the pre-existing processes.
    log.debug('Signaling existing processes to shutdown.')
    for pid in existing_processes:
        try:
            os.kill(pid, signal.SIGUSR1)
            log.info('Shutting down old process: %s', pid)
        except OSError:
            log.debug('Failed to shutdown %s (it may have already terminated)',
                pid)

    # Success
    global deployed_symlink_value
    if watch_symlink:
        deployed_symlink_value = read_symlink()
    return

# Make sure that the cgroup exists first.
if not os.path.exists('/sys/fs/cgroup/cpu/{0}'.format(cgroup)):
    os.mkdir('/sys/fs/cgroup/cpu/{0}'.format(cgroup))
if not os.path.exists('/sys/fs/cgroup/memory/{0}'.format(cgroup)):
    os.mkdir('/sys/fs/cgroup/memory/{0}'.format(cgroup))

# Join the cgroup.
log.debug('Joining the cgroup: %s', cgroup)
with open('/sys/fs/cgroup/cpu/{0}/tasks'.format(cgroup), 'a') as fd:
    fd.write('{0}\n'.format(os.getpid()))
with open('/sys/fs/cgroup/memory/{0}/tasks'.format(cgroup), 'a') as fd:
    fd.write('{0}\n'.format(os.getpid()))

# When this process starts we want to start a deploy right away.
start_deploy = True

# Marks how many health checking failures we have had in a row.
health_check_failures = 0

# Main program loop.
while True:
    # Clear out any children.
    wait_for_children()

    # Branch on three conditions:
    #  1) We need to perform a deploy.
    #  2) All managed tasks have died so we need to start a new one.
    #  3) A file needs watch so we do this, waiting for a signal or the file
    #     to change so we can start a deploy.
    #  4) Nothing else is needed so we sleep for a day waiting for a deploy
    #     signal to be triggered.
    if start_deploy:
        log.info('New deploy requested.')
        deploy()
    elif not cgroup_processes():
        log.warning('Current managed process has died.')
        deploy()
    elif watch_symlink != '':
        # If we are tasked with watching a specific symlink for changes then
        # we do it here. get_events will be interrupted by a SIGHUP signal
        # which we can catch to start a deploy. A return from get_events will
        # also be evaluated and if the file has changed then a deploy will be
        # started.
        import inotifyx
        dirname, filename = os.path.split(watch_symlink)
        fd = inotifyx.init()
        try:
            # Watch the directory, if it changes then we need to see if the
            # change was in the file we specifically care about. While we
            # have the watch in place we compare the symlink to what was last
            # deployed, if it is different then we don't bother waiting, we
            # just set start_deploy and then loop.
            wd = inotifyx.add_watch(fd, dirname, inotifyx.IN_DELETE)
            if deployed_symlink_value != read_symlink():
                log.info('Symlink changed from "%s" to "%s", deploying.',
                        deployed_symlink_value, read_symlink())
                start_deploy = True
            else:
                events = inotifyx.get_events(fd, 24*60*60)
                if deployed_symlink_value != read_symlink():
                    log.info('Symlink changed from "%s" to "%s", deploying.',
                            deployed_symlink_value, read_symlink())
                    start_deploy = True
            inotifyx.rm_watch(fd, wd)
        except IOError as e:
            if e.errno == 2:
                # Errno2 is thrown when the file we are attempting to watch
                # does not exist. If this happens then we fall back to a
                # simple sleep loop. Sleep will be interrupted by a signal.
                time.sleep(1)
            elif e.errno == 4:
                # Errno 4 is used when a syscall gets interrupted. This will
                # most likely be due to a signal so we repeat our loop to check
                # the various conditions.
                pass
        finally:
            os.close(fd)
    elif health_check_failures > max_health_check_failures:
        # The stead state health checker has failed too many times in a row.
        # We need to initiate a deploy cycle.
        log.warning('Health check failed %d times, Initiating a deploy.',
                health_check_failures)
        deploy()
        health_check_failures = 0
    else:
        # Start by performing a health check, then sleep for the proper
        # interval depending on the health check status. Note that the
        # sleep will be interrupted by a signal if any process we are watching
        # dies so its okay to sleep here.
        if not healthcheck(port):
            log.info('Health check failed.')
            health_check_failures += 1
            time.sleep(failed_health_check_interval)
        else:
            health_check_failures = 0
        time.sleep(health_check_interval)
