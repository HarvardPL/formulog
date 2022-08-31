#!/usr/bin/env python3

import argparse
import random

def make_graph(n, p):
    if n < 0:
        raise Exception("Cannot have a graph with a negative number of vertices")
    if p < 0 or p > 1:
        raise Exception("Edge probability is out of range [0, 1]")
    for i in range(n):
        for j in range(n):
            if random.random() < p:
                yield (i, j)

def main():
    desc = """Generate and output a random graph according to the Erdős-Rényi
    model. The graph is output as tab-separated pairs of integers representing
    vertices, one edge per line."""
    parser = argparse.ArgumentParser(description=desc)
    parser.add_argument("n", type=int, help="number of vertices")
    parser.add_argument("p", type=float, help="probability of a given edge existing")
    args = parser.parse_args()
    for (i, j) in make_graph(args.n, args.p):
        print("%d\t%d" % (i, j))

if __name__ == "__main__":
    main()
