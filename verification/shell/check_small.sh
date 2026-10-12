#!/usr/bin/env bash
# check_small.sh -- bash integer arithmetic only: for every binary circular word of length
# n <= NMAX, count the distinct abelian squares and check that the minimum is floor((n-1)/2)
# and that the words attaining it are those of the paper (Theorem 1.1).
# A word is an n-bit integer (bit i = letter i, 1 = a). Prints "ALL OK" on success.
set -u
NMAX=${NMAX:-10}

popcount() { local v=$1 c=0; while (( v )); do (( c += v & 1, v >>= 1 )); done; echo $c; }

rotl() { local w=$1 r=$2 n=$3; echo $(( ((w >> r) | (w << (n - r))) & ((1 << n) - 1) )); }

failed=0
for (( n = 1; n <= NMAX; n++ )); do
  mask=$(( (1 << n) - 1 ))
  # the family of extremal words, generated from its description
  declare -A fam=()
  add_conj() { local u=$1 r; for (( r = 0; r < n; r++ )); do fam[$(rotl "$u" "$r" "$n")]=1; done; }
  if (( n % 2 == 1 )); then
    for u in $mask $(( mask >> 1 )); do add_conj "$u"; add_conj $(( ~u & mask )); done
  else
    for (( k = 1; k < n; k += 2 )); do u=$(( (1 << k) - 1 )); add_conj "$u"; add_conj $(( ~u & mask )); done
    if (( n % 4 == 2 )); then
      alt=0; for (( i = 0; i < n; i += 2 )); do (( alt |= 1 << i )); done
      add_conj "$alt"; add_conj $(( ~alt & mask ))
    fi
  fi
  target=$(( (n - 1) / 2 )); minD=1000; bad=0; ext=0
  for (( w = 0; w <= mask; w++ )); do
    ww=$(( w | (w << n) ))          # the word written twice
    declare -A seen=()
    D=0
    for (( m = 1; 2 * m <= n; m++ )); do
      for (( i = 0; i < n; i++ )); do
        f=$(( (ww >> i) & ((1 << (2 * m)) - 1) ))
        lo=$(( f & ((1 << m) - 1) )); hi=$(( f >> m ))
        if (( $(popcount $lo) == $(popcount $hi) )); then
          key="$m:$f"
          if [[ -z ${seen[$key]+x} ]]; then seen[$key]=1; (( D++ )); fi
        fi
      done
    done
    unset seen
    (( D < minD )) && minD=$D
    (( D == target )) && (( ext++ ))
    infam=0; [[ -n ${fam[$w]+x} ]] && infam=1
    if (( (D == target) != infam )); then bad=1; fi
  done
  unset fam
  status=ok; if (( minD != target || bad )); then status=FAIL; failed=1; fi
  echo "n=$n  min D=$minD  floor((n-1)/2)=$target  extremal words=$ext  $status"
done
if (( failed )); then echo "SOME CHECKS FAILED"; exit 1; fi
echo "ALL OK"
