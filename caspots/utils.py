
import itertools
import sys

def dbg(msg):
    print(msg, file=sys.stderr)

def warning(msg):
    print("WARNING: %s" % msg, file=sys.stderr)

def partitions(elts):
    if not elts:
        yield [()]
    elif len(elts) == 1:
        yield [tuple(elts)]
    else:
        elt = elts[0]
        for p in partitions(elts[1:]):
            yield [(elt,)] + p
            for n, subset in enumerate(p):
                yield p[:n] + [subset + (elt,)] + p[n+1:]

def async_interleavings(updates):
    for seq in itertools.permutations(updates):
        yield [(n,) for n in seq]

def general_interleavings(updates):
    for p in partitions(updates):
        for seq in itertools.permutations(p):
            yield seq

