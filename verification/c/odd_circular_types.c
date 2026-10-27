/* Types of abelian squares in binary circular words of odd length.
   For every binary circular word w of odd length n (words with more a's
   than b's are omitted, by complementation) and every half-length m with
   2m < n, z_m(w) is the number of values c such that some factor uv of w
   with |u| = |v| = m has |u|_a = |v|_a = c.  The program checks
     N(w) = sum_m z_m(w) >= (n-1)/2            (Conjecture)
     z_1(w) + ... + z_k(w) >= k for all k      (its prefix form)
   and prints the least value of N, the number of words attaining it and
   the number of violations.  Usage: ./odd_circular_types n  (n odd, n <= 31). */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s n\n", argv[0]); return 2; }
  int n = atoi(argv[1]);
  if (n < 3 || n > 31 || n % 2 == 0) { fprintf(stderr, "n must be odd, 3 <= n <= 31\n"); return 2; }
  int half = (n - 1) / 2;
  long words = 0, attain = 0, failN = 0, failPrefix = 0, minN = 1L << 30;
  for (unsigned long w = 0; w < (1UL << n); w++) {
    int ta = __builtin_popcountl(w);
    if (ta > n / 2) continue;
    unsigned long d = w | (w << n) | (w << (2 * n));
    long N = 0, prefixok = 1;
    for (int m = 1; m <= half; m++) {
      unsigned long seen = 0, mask = (1UL << m) - 1;
      for (int i = 0; i < n; i++) {
        int cu = __builtin_popcountl((d >> i) & mask);
        int cv = __builtin_popcountl((d >> (i + m)) & mask);
        if (cu == cv) seen |= 1UL << cu;
      }
      N += __builtin_popcountl(seen);
      if (N < m) prefixok = 0;
    }
    words++;
    if (N < minN) { minN = N; attain = 0; }
    if (N == minN) attain++;
    if (N < half) failN++;
    if (!prefixok) failPrefix++;
  }
  printf("n=%d words=%ld minN=%ld (claimed %d) attaining=%ld violations: bound %ld, prefix form %ld\n",
         n, words, minN, half, attain, failN, failPrefix);
  return (failN || failPrefix) ? 1 : 0;
}
