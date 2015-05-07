import argparse
timeout = 10  # in seconds
force_fm = True  # If true, will force Polya to use Fourier Motzkin methods. Otherwise, will use
                  # polytope methods if available.
force_smt = False  # If true, will produce smt2 format output when simplify is called

import smtlib2polya
import sys
import signal
from os import listdir, devnull
from os.path import isfile, join
from timeit import default_timer
stdout = sys.stdout


class TimerException(Exception):
    def __init__(self):
        super(TimerException, self).__init__()


def alert(num, frame):
    print "Error: timed out!"
    raise TimerException


#sys.stdout = open(output, 'w')


def batch_test(file, time, forcefm, forcesmt):
    results = {-1: 0, 0: 0, 1: 0}
    sys.stdout = open(devnull, 'w')
    timer = default_timer()
    r = 0
    try:
        signal.signal(signal.SIGALRM, alert)
        signal.alarm(timeout)
        r = smtlib2polya.run_smt_file(file, (forcefm or force_fm), (forcesmt or force_smt))
    except Exception as e:
        r = 0
    finally:
        sys.stdout = stdout
        print r

def interrupt_handler(signal, frame):
    sys.exit(1)

signal.signal(signal.SIGINT, interrupt_handler)

#batch_test()
if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Process smt file using Polya.")
    parser.add_argument('file', metavar='file', type=str, help="path to smt file")
    parser.add_argument('-t', type=int,  help="timeout (in sec)")
    parser.add_argument('-f', action="store_true", help="force FM")
    parser.add_argument('-s', action="store_true",  help="force SMT output from simplify")
    args = parser.parse_args()
    print args.file
    batch_test(args.file, (args.t if args.t else timeout), args.f, args.s)