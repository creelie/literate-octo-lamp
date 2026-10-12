"""verify_simpson.py -- Simpson's Conjecture 0.6, checked from the definitions.

A binary circular word of length n is a string over {a, b}; its factors are the words
(w rotated by i)[:L] with 0 <= i < n and 1 <= L <= n. A factor s is an abelian square if
s = uv with u nonempty and P(u) = P(v), P the Parikh vector; every split of s is tried.
D(w) is the number of distinct abelian squares among the factors.

For every n <= NMAX and every word of length n this checks:
  * min D = floor((n-1)/2);
  * Conjecture 0.6 (a): for odd n the words with D = (n-1)/2 are the conjugates of
    a^n, a^(n-1) b and their complements;
  * Conjecture 0.6 (b) as stated: for even n the minimum is (n-2)/2, and its list
    (conjugates of a^k b^(n-k), k odd, and complements) is complete exactly when
    n is not 2 mod 4 or n = 2;
  * the corrected (b): the list together with the conjugates of (ab)^(n/2) for n = 2 mod 4.
"""
from collections import Counter
from itertools import product

NMAX = 12


def rotate(w, i):
    return w[i:] + w[:i]


def factors(w):
    n = len(w)
    return {rotate(w, i)[:L] for i in range(n) for L in range(1, n + 1)}


def is_abelian_square(s):
    return any(Counter(s[:j]) == Counter(s[j:]) for j in range(1, len(s) + 1))


def D(w):
    return sum(1 for s in factors(w) if is_abelian_square(s))


def conjugates(u):
    return {rotate(u, r) for r in range(len(u))}


def complement(u):
    return u.translate(str.maketrans("ab", "ba"))


def with_complements(words):
    out = set()
    for u in words:
        out |= conjugates(u) | conjugates(complement(u))
    return out


def main():
    ok = True
    for n in range(1, NMAX + 1):
        values = {"".join(t): D("".join(t)) for t in product("ab", repeat=n)}
        m = min(values.values())
        extremal = {w for w, d in values.items() if d == m}
        if n % 2 == 1:
            simpson = with_complements(["a" * n, "a" * (n - 1) + "b"])
            corrected = simpson
            bound = (n - 1) // 2
        else:
            simpson = with_complements(["a" * k + "b" * (n - k) for k in range(1, n, 2)])
            corrected = simpson | (with_complements(["ab" * (n // 2)]) if n % 4 == 2 else set())
            bound = (n - 2) // 2
        line_ok = (m == (n - 1) // 2 == bound and extremal == corrected
                   and (extremal == simpson) == (n % 2 == 1 or n % 4 == 0 or n == 2))
        extra = sorted(extremal - simpson)
        print(f"n={n:2d}  min D={m}  extremal words={len(extremal):3d}  "
              f"missing from Simpson's list: {extra[:2]}{'...' if len(extra) > 2 else ''}  "
              f"{'ok' if line_ok else 'FAIL'}")
        ok = ok and line_ok
    w = "ababab"
    squares = sorted(s for s in factors(w) if is_abelian_square(s))
    counter_ok = squares == ["abab", "baba"] and w not in with_complements(
        ["a" * k + "b" * (6 - k) for k in range(0, 7)])
    print(f"ababab: abelian squares {squares}; not a conjugate of a^k b^(6-k) or its complement: "
          f"{counter_ok}")
    ok = ok and counter_ok
    print("ALL OK" if ok else "SOME CHECKS FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
