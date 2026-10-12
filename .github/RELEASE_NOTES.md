**The minimum number of distinct abelian squares in a binary circular word**, by Deep Bhattacharjee.

Every binary circular word of length n contains at least ⌊(n−1)/2⌋ distinct abelian squares. The paper proves this and determines the words attaining the bound, which settles Conjecture 0.6 of J. Simpson ([arXiv:1802.04481](https://arxiv.org/abs/1802.04481)): part (a) holds, and the list of extremal words in part (b) misses (ab)^{n/2} for n ≡ 2 (mod 4), n ≥ 6 (for example D(ababab) = 2).

| Step | Content |
|---|---|
| Lemmas 2.2–2.5 | Pairs (last letter of the left half, its count) of the abelian squares of half-length m; the bijection between half-lengths m and n − m; every column C_ℓ(k), 1 ≤ k < \|w\|_ℓ, is nonempty |
| Theorem 2.6 | D(w) ≥ ⌊(n−1)/2⌋ |
| Theorem 3.1 | Rigid words with a tight letter are conjugates of ℓ^t ℓ̄^{n−t} with t odd or t = n, or of (ℓℓ̄)^{n/2} |
| Theorem 1.1 | The words with D(w) = ⌊(n−1)/2⌋ |

The proofs are by hand and formalized in Lean 4 with Mathlib: the six main theorems, including `conjectureA` and `not_conjectureB`, depend only on the axioms propext, Classical.choice and Quot.sound. Independent checks: C (every word of length n ≤ 22), C++ (every necklace, n ≤ 28), Python (from the definitions, n ≤ 12), Julia (every lemma of the proof, n ≤ 16) and Bash (n ≤ 10).

Files:
- `simpson-abelian-squares.pdf`: the paper
- `simpson-abelian-squares-tex.zip`: LaTeX source (`main.tex`, `elsarticle.cls`)
- `simpson-abelian-squares-arxiv.tar.gz`: the same source, ready for arXiv
- `MasterSimpsonCircularAbelianSquaresZip.zip`: every file of the repository with the three files above

Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.
