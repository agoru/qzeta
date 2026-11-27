"""lem:S (sums) on random families of masses and zeros: k is an index of a largest term, so every row meets the
hypotheses (standard library only)."""
import random
from fractions import Fraction

KIND = "witness"


def rows(n=200, seed=20261106):
    rng = random.Random(seed)
    for _ in range(n):
        N = rng.randint(1, 6)
        a = [Fraction(rng.randint(0, 40), rng.randint(1, 12)) for _ in range(N)]
        k = 1 + max(range(N), key=lambda i: a[i])
        yield {"N": N, "a[]": [str(x) for x in a], "k": k}
