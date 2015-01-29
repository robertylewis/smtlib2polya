smt_dir = '../keymaera-smt2/'
output = smt_dir + 'results.out'
timeout = 10 # in seconds

import smtlib2polya
import sys
import signal
from os import listdir
from os.path import isfile, join
from timeit import default_timer
stdout = sys.stdout

class TimerException(Exception):
    def __init__(self):
        super(TimerException, self).__init__()

def alert(num, frame):
    raise TimerException

def write_shell(s):
    o = sys.stdout
    sys.stdout = stdout
    print s
    sys.stdout = o

files = sorted([smt_dir+f for f in listdir(smt_dir) if isfile(join(smt_dir,f)) and f[-4:] == 'smt2'])
sys.stdout = open(output, 'w')

results = {-1:0, 0:0, 1:0}

timer = default_timer()

for i, f in enumerate(files):
    write_shell('{0!s}: {1}'.format(i, f))
    try:
        signal.signal(signal.SIGALRM, alert)
        signal.alarm(timeout)
        results[smtlib2polya.run_smt_file(f)] += 1
        # except TimerException as e:
        # 	print 'Error: timeout.'
        # 	write_shell('Error: timeout.')
        # 	results[0] += 1
    except Exception as e:
        if isinstance(e, TimerException):
            print 'Error: timeout.'
            write_shell('Error: timeout.')
            results[0] += 1
        else:
            print 'Error:', e.message
            write_shell(e.message)
            results[0] += 1

timer = round(default_timer() - timer, 1)
s = 'Ran {0!s} examples in {1!s} seconds.\n'.format(len(files), timer)
s += '{0!s} successes, {1!s} failures, and {2!s} errors.'.format(results[1], results[-1], results[0])
print s
write_shell(s)

