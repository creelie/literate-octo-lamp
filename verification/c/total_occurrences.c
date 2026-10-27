/* Least number MTL(n) of occurrences of abelian squares in a binary word
   of length n (Question 0.7 of Simpson's survey), by exhaustive search over
   the words with at most n/2 letters a.  Prints MTL(n), the number of such
   words attaining it and one of them.  Usage: ./total_occurrences nmin nmax */
#include <stdio.h>
#include <stdlib.h>
int main(int argc, char **argv) {
  if (argc < 3) { fprintf(stderr, "usage: %s nmin nmax\n", argv[0]); return 2; }
  int nmin = atoi(argv[1]), nmax = atoi(argv[2]);
  if (nmin < 1 || nmax > 31 || nmin > nmax) return 2;
  for (int n = nmin; n <= nmax; n++) {
    long best = 1L << 30, count = 0; unsigned long arg = 0;
    for (unsigned long w = 0; w < (1UL << n); w++) {
      if (__builtin_popcountl(w) > n / 2) continue;
      long occ = 0;
      for (int m = 1; 2 * m <= n && occ <= best; m++) {
        unsigned long mask = (1UL << m) - 1;
        for (int i = 0; i + 2 * m <= n; i++)
          if (__builtin_popcountl((w >> i) & mask) == __builtin_popcountl((w >> (i + m)) & mask)) occ++;
      }
      if (occ < best) { best = occ; count = 0; arg = w; }
      if (occ == best) count++;
    }
    printf("n=%d MTL=%ld attaining(words with #a<=n/2)=%ld example=", n, best, count);
    for (int i = 0; i < n; i++) putchar((arg >> i) & 1 ? 'a' : 'b');
    printf("\n"); fflush(stdout);
  }
  return 0;
}
