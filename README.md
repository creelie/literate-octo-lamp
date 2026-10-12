# The minimum number of distinct abelian squares in a binary circular word

Author: Deep Bhattacharjee (ORCID 0000-0003-0466-750X).

This repository settles Conjecture 0.6 of J. Simpson, "Solved and unsolved
problems about abelian squares" ([arXiv:1802.04481](https://arxiv.org/abs/1802.04481)):

> The minimum number of distinct abelian squares in a circular word of length n is:
> (a) (n-1)/2 if n is odd and this bound is attained only by a^n, a^{n-1}b and
> their complements and conjugates.
> (b) (n-2)/2 if n is even and this bound is attained only by a^k b^{n-k} and its
> complement and their conjugates, where k ∈ {1, 3, 5, ..., n-1}.

## Result

**Theorem.** Every binary circular word w of length n >= 1 has at least
floor((n-1)/2) distinct abelian squares among its factors of length at most n.
Equality holds exactly for the conjugates of

- a^n, b^n, a^{n-1}b, b^{n-1}a when n is odd;
- a^k b^{n-k} with k odd, and (ab)^{n/2} when n = 2 (mod 4), when n is even.

So part (a) of the conjecture holds, the minimum in part (b) is correct, and
the list of extremal words in part (b) is incomplete exactly for
n = 2 (mod 4), n >= 6: the circular word ababab has the two abelian squares
abab and baba and is not a conjugate of a^k b^{6-k} or its complement.

The proof counts, for each half-length m, the pairs (last letter of the left
half, its number of occurrences there) over all abelian squares of half-length
m; these pairs for m and n-m are in bijection, and each pair (l, k) with
1 <= k < |w|_l occurs for some m. Equality forces each count to be exact, and
a case analysis of the runs of one letter gives the extremal words.

## Contents

| Path | Contents |
|---|---|
| `paper/` | LaTeX source (`main.tex`, Elsevier `elsarticle` class) and the compiled `main.pdf` |
| `verification/lean/` | Lean 4 + Mathlib formalization (13 files, 2230 lines); `Circ/Statement.lean` holds the definitions, `Circ/Simpson.lean` the theorems |
| `verification/c/` | `circsq.c`: every binary word of length n <= 22 |
| `verification/cpp/` | `necklaces.cpp`: one word per necklace, n <= 28 |
| `verification/python/` | `verify_simpson.py`: from the definitions (all rotations, all splits, Parikh vectors), n <= 12 |
| `verification/julia/` | `verify_lemmas.jl`: every lemma of the proof on every word of length n <= 16 |
| `verification/shell/` | `check_small.sh`: Bash integer arithmetic only, n <= 10 |
| `scripts/run_all.sh` | runs the Lean build, the axiom check and all programs |
| `scripts/build_paper.sh` | builds the files in `dist/` |
| `journal/JOURNAL.md` | target journal, format rules and AI policy |
| `dist/` | the paper PDF, the LaTeX source zip, the arXiv tarball and `MasterSimpsonCircularAbelianSquaresZip.zip`, which holds every file of the repository |

## Lean statements

```lean
theorem min_distinct {n : ℕ} (hn : 0 < n) :
    IsLeast {d | ∃ w : List Bool, w.length = n ∧ numDistinctAbelianSquares w = d}
      ((n - 1) / 2)

theorem extremal_odd {w : List Bool} (ho : w.length % 2 = 1) :
    numDistinctAbelianSquares w = (w.length - 1) / 2 ↔
      IsConj w (blk w.length w.length) ∨ IsConj w (blk (w.length - 1) w.length) ∨
        IsConj w (compl (blk w.length w.length)) ∨
          IsConj w (compl (blk (w.length - 1) w.length))

theorem extremal_even {w : List Bool} (he : w.length % 2 = 0) (hn : 0 < w.length) :
    numDistinctAbelianSquares w = (w.length - 2) / 2 ↔
      (∃ k, k % 2 = 1 ∧ k < w.length ∧
          (IsConj w (blk k w.length) ∨ IsConj w (compl (blk k w.length)))) ∨
        (w.length % 4 = 2 ∧ (IsConj w (alt w.length) ∨ IsConj w (compl (alt w.length))))

theorem conjectureA : ConjectureA
theorem not_conjectureB : ¬ ConjectureB
```

Words are `List Bool` with a = `true`; `numDistinctAbelianSquares w` counts the
distinct words `(w.rotate i).take L`, 0 <= i < n, 1 <= L <= n, of the form uv
with u nonempty and the same number of each letter in u and v. `ConjectureA`
and `ConjectureB` state parts (a) and (b) of Simpson's conjecture.
`#print axioms` reports `[propext, Classical.choice, Quot.sound]` for each of
the six main theorems (`verification/lean/Axioms.lean`); there is no `sorry`,
`admit`, `native_decide` or added axiom.

## Running the checks

Requirements: elan (Lean 4.34.1, fetched from `verification/lean/lean-toolchain`),
python3, julia, a C compiler and a C++17 compiler.

    scripts/run_all.sh          # Lean build (with the Mathlib cache), axiom check, all programs
    LEAN=0 scripts/run_all.sh   # programs only

To build the paper and the release files: `scripts/build_paper.sh`.

## License

MIT, see `LICENSE`.
