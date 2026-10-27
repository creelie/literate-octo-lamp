/* Minimum numbers of abelian squares in binary (linear) words of length n,
   counted as distinct factors (D) and up to equivalence (N: same length
   and same number of a's), for all n up to the argument.  The program also
   counts the words with exactly floor(n/4) distinct abelian squares that
   contain a non-trivial one (not of the form a^2i or b^2i).
   Usage: ./linear_minima nmax  (nmax <= 28). */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  if (argc < 2) { fprintf(stderr, "usage: %s nmax\n", argv[0]); return 2; }
  int nmax = atoi(argv[1]);
  if (nmax < 2 || nmax > 28) { fprintf(stderr, "nmax must be between 2 and 28\n"); return 2; }
  for (int n = 2; n <= nmax; n++) {
    long minD = 1L << 30, minN = 1L << 30, nontrivialAtFloor = 0;
    unsigned *buf = malloc(sizeof(unsigned) * (n + 1));
    for (unsigned w = 0; w < (1u << n); w++) {
      if (__builtin_popcount(w) > n / 2) continue;
      long D = 0, N = 0; int nontrivial = 0;
      for (int m = 1; 2 * m <= n; m++) {
        int cnt = 0; unsigned seen = 0; unsigned mask = (1u << m) - 1;
        for (int i = 0; i + 2 * m <= n; i++) {
          unsigned u = (w >> i) & mask, v = (w >> (i + m)) & mask;
          int pu = __builtin_popcount(u);
          if (pu != __builtin_popcount(v)) continue;
          unsigned s = (w >> i) & ((1u << (2 * m)) - 1);
          int dup = 0;
          for (int t = 0; t < cnt; t++) if (buf[t] == s) { dup = 1; break; }
          if (!dup) { buf[cnt++] = s; if (s != 0 && s != ((1u << (2 * m)) - 1)) nontrivial = 1; }
          seen |= 1u << pu;
        }
        D += cnt; N += __builtin_popcount(seen);
      }
      if (D < minD) minD = D;
      if (N < minN) minN = N;
      if (D == n / 4 && nontrivial) nontrivialAtFloor++;
    }
    free(buf);
    printf("n=%d floor(n/4)=%d minD=%ld minN=%ld words with D=floor(n/4) and a non-trivial square: %ld\n",
           n, n / 4, minD, minN, nontrivialAtFloor);
    fflush(stdout);
  }
  return 0;
}
