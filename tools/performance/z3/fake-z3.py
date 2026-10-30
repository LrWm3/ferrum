#!/usr/bin/env python3
"""Fake solver for wrapper tests; never invokes Z3."""
import json, os, signal, sys, time
mode = sys.argv[1]
if mode == '--version':
    print('fake Z3 version', flush=True)
elif mode == 'echo':
    print(json.dumps({'argv':sys.argv[1:],'stdin':sys.stdin.read()}), flush=True)
    print('fake stderr', file=sys.stderr, flush=True)
elif mode == 'exit':
    sys.exit(int(sys.argv[2]))
elif mode == 'signal':
    os.kill(os.getpid(), int(sys.argv[2]))
elif mode == 'wait':
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    print(os.getpid(), flush=True)
    while True: time.sleep(1)
else:
    sys.exit(123)
