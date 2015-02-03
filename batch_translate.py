smt_dir = '../keymaera-smt2/'
output = smt_dir + 'results.out'
timeout = 10  # in seconds
force_fm = False  # If true, will force Polya to use Fourier Motzkin methods. Otherwise, will use
                  # polytope methods if available.

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
    print "Error: timed out!"
    write_shell("Error: timed out!")
    raise TimerException


def write_shell(s):
    o = sys.stdout
    sys.stdout = stdout
    print s
    sys.stdout = o

files = sorted([smt_dir+f for f in listdir(smt_dir)
                if isfile(join(smt_dir, f)) and f[-4:] == 'smt2'])
sys.stdout = open(output, 'w')

def poly_fm_compare():
    results = {-1: 0, 0: 0, 1: 0}
    results2 = {-1: 0, 0: 0, 1: 0}
    comps = {}

    timer = default_timer()

    for i, f in enumerate(files):
        write_shell('{0!s}: {1}'.format(i+1, f))
        print '\n{0!s}: {1}\n'.format(i+1, f)
        r = 0
        try:
            signal.signal(signal.SIGALRM, alert)
            signal.alarm(timeout)
            r = smtlib2polya.run_smt_file(f, force_fm)
            # except TimerException as e:
            # 	print 'Error: timeout.'
            # 	write_shell('Error: timeout.')
            # 	results[0] += 1
        except Exception as e:
            print 'Error:', e.message
            write_shell(e.message)
            r = 0
            raise e
        finally:
            results[r] += 1
            comps[f] = [r]

        r = 0
        try:
            signal.signal(signal.SIGALRM, alert)
            signal.alarm(timeout)
            r = smtlib2polya.run_smt_file(f, not force_fm)
            # except TimerException as e:
            # 	print 'Error: timeout.'
            # 	write_shell('Error: timeout.')
            # 	results[0] += 1
        except Exception as e:
            print 'Error:', e.message
            write_shell(e.message)
            r = 0
        finally:
            results2[r] += 1
            comps[f].append(r)

    errors = {-1:"failed", 0:"error or time", 1:"succeeded"}

    timer = round(default_timer() - timer, 1)
    s = 'Ran {0!s} examples in {1!s} seconds.\n'.format(len(files), timer)
    s += 'Poly: {0!s} successes, {1!s} failures, and {2!s} errors.\n'.format(
        results[1], results[-1], results[0]
    )
    s += 'FM: {0!s} successes, {1!s} failures, and {2!s} errors.\n'.format(
        results2[1], results2[-1], results2[0]
    )
    s += '\nPoly and FM differed on:\n\n'
    for k in [key for key in comps.keys() if comps[key][0] != comps[key][1]]:
        s += k + '\n'
        s += '  Poly {0}, FM {1}\n'.format(errors[comps[k][0]], errors[comps[k][1]])
    print s
    write_shell(s)

def batch_test():
    results = {-1: 0, 0: 0, 1: 0}

    timer = default_timer()

    for i, f in enumerate(files):
        write_shell('{0!s}: {1}'.format(i+1, f))
        print '\n{0!s}: {1}\n'.format(i+1, f)
        r = 0
        try:
            signal.signal(signal.SIGALRM, alert)
            signal.alarm(timeout)
            r = smtlib2polya.run_smt_file(f, force_fm)
            # except TimerException as e:
            # 	print 'Error: timeout.'
            # 	write_shell('Error: timeout.')
            # 	results[0] += 1
        except Exception as e:
            print 'Error:', e.message
            write_shell(e.message)
            r = 0
        finally:
            results[r] += 1

    errors = {-1:"failed", 0:"error or time", 1:"succeeded"}

    timer = round(default_timer() - timer, 1)
    s = 'Ran {0!s} examples in {1!s} seconds.\n'.format(len(files), timer)
    s += '{0!s} successes, {1!s} failures, and {2!s} errors.\n'.format(
        results[1], results[-1], results[0]
    )
    print s
    write_shell(s)

batch_test()