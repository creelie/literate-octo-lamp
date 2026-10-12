/*
 * circsq.c -- distinct abelian squares in binary circular words.
 *
 * A binary circular word of length n is an n-bit integer w (bit i = letter i, 1 = a, 0 = b).
 * Its factors are the words of length L <= n read cyclically from each of the n positions.
 * An abelian square is a factor uv with |u| = |v| >= 1 and the same number of a's in u and v.
 * D(w) is the number of distinct abelian squares.
 *
 * For every n <= NMAX and every word w of length n the program computes D(w) and checks
 *   (1) min_w D(w) = floor((n-1)/2),
 *   (2) the words with D(w) = floor((n-1)/2) are exactly the conjugates of
 *         n odd:  a^n, a^(n-1) b and their complements;
 *         n even: a^k b^(n-k) with k odd and their complements, and (ab)^(n/2) when n = 2 mod 4;
 *       the family is generated independently from its description;
 *   (3) for n = 6: D((ab)^3) = 2, and (ab)^3 is not a conjugate of a^k b^(6-k) or its complement.
 * It prints the number of extremal words for each n and "ALL OK" at the end.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define NMAX 22

static uint32_t *stamp;         /* stamp[key] = id of the last word that produced key */
static unsigned char *extremal; /* membership of the predicted family */

static uint32_t rotl(uint32_t w, int r, int n) {
  uint32_t mask = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
  r %= n;
  if (r == 0) return w & mask;
  return ((w >> r) | (w << (n - r))) & mask;
}

/* the factor of length L starting at position i, as an L-bit integer */
static uint32_t factor(uint32_t w, int n, int i, int L) {
  uint32_t f = 0;
  for (int t = 0; t < L; t++) f |= ((w >> ((i + t) % n)) & 1u) << t;
  return f;
}

static int D(uint32_t w, int n, uint32_t id) {
  int count = 0;
  for (int m = 1; 2 * m <= n; m++) {
    int L = 2 * m;
    for (int i = 0; i < n; i++) {
      uint32_t f = factor(w, n, i, L);
      uint32_t left = f & ((1u << m) - 1), right = f >> m;
      if (__builtin_popcount(left) != __builtin_popcount(right)) continue;
      uint32_t key = f | (1u << L); /* the length is encoded by the leading bit */
      if (stamp[key] != id) { stamp[key] = id; count++; }
    }
  }
  return count;
}

static uint32_t block(int k, int n) { return (k >= 32) ? 0xffffffffu : ((1u << k) - 1); } /* a^k b^(n-k) */

static void mark_conjugates(uint32_t w, int n) {
  for (int r = 0; r < n; r++) extremal[rotl(w, r, n)] = 1;
}

int main(void) {
  int fail = 0;
  stamp = calloc((size_t)1 << (NMAX + 1), sizeof(uint32_t));
  extremal = malloc((size_t)1 << NMAX);
  if (!stamp || !extremal) { fprintf(stderr, "out of memory\n"); return 2; }
  uint32_t id = 0;
  for (int n = 1; n <= NMAX; n++) {
    uint32_t N = 1u << n, mask = N - 1;
    memset(extremal, 0, N);
    if (n % 2 == 1) {
      uint32_t fam[2] = {block(n, n), block(n - 1, n)};
      for (int j = 0; j < 2; j++) { mark_conjugates(fam[j], n); mark_conjugates(~fam[j] & mask, n); }
    } else {
      for (int k = 1; k < n; k += 2) {
        mark_conjugates(block(k, n), n);
        mark_conjugates(~block(k, n) & mask, n);
      }
      if (n % 4 == 2) {
        uint32_t alt = 0;
        for (int i = 0; i < n; i += 2) alt |= 1u << i;
        mark_conjugates(alt, n);
        mark_conjugates(~alt & mask, n);
      }
    }
    int target = (n - 1) / 2, minD = 1 << 30;
    long attained = 0, family = 0, mismatch = 0;
    for (uint32_t w = 0; w < N; w++) {
      int d = D(w, n, ++id);
      if (d < minD) minD = d;
      if (d == target) attained++;
      if (extremal[w]) family++;
      if ((d == target) != (extremal[w] != 0)) mismatch++;
    }
    int ok = (minD == target) && mismatch == 0 && attained == family;
    printf("n=%2d  min D=%d  floor((n-1)/2)=%d  extremal words=%ld  family size=%ld  %s\n",
           n, minD, target, attained, family, ok ? "ok" : "FAIL");
    if (!ok) fail = 1;
  }
  /* the counterexample to Conjecture 0.6 (b) */
  {
    int n = 6;
    uint32_t alt = 0x15; /* positions 0, 2, 4: ababab */
    int d = D(alt, n, ++id);
    int conj = 0;
    for (int k = 0; k <= n; k++)
      for (int r = 0; r < n; r++)
        if (rotl(block(k, n), r, n) == alt || rotl(~block(k, n) & 63u, r, n) == alt) conj = 1;
    printf("(ab)^3: D=%d, conjugate of a^k b^(6-k) or complement: %s\n", d, conj ? "yes" : "no");
    if (d != 2 || conj) fail = 1;
  }
  free(stamp);
  free(extremal);
  puts(fail ? "SOME CHECKS FAILED" : "ALL OK");
  return fail;
}
