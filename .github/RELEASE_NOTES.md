**The minimum number of distinct abelian squares in a binary circular word**, by Deep Bhattacharjee.

We prove that every binary circular word of length n contains at least ⌊(n−1)/2⌋ distinct abelian squares, and we determine all words attaining this bound. This settles Conjecture 0.6 of J. Simpson ([arXiv:1802.04481](https://arxiv.org/abs/1802.04481)): part (a) holds, and the list of extremal words in part (b) misses (ab)^{n/2} for n ≡ 2 (mod 4), n ≥ 6 (for example D(ababab) = 2).

Version 2.1.0 makes Deep Bhattacharjee the sole author and cites this release in the data availability statement. Version 2.0.0 added the journal format for Theoretical Computer Science: MSC 2020 codes (Primary 68R15; Secondary 05A05, 68V15), three schematic figures, and the data availability, competing interests and funding statements. The mathematics is that of v1.0.0.

| Step | Content |
|---|---|
| Lemmas 2.2–2.5 | Pairs (last letter of the left half, its count) of the abelian squares of half-length m; the bijection between half-lengths m and n − m; every column C_ℓ(k), 1 ≤ k < \|w\|_ℓ, is nonempty |
| Theorem 2.6 | D(w) ≥ ⌊(n−1)/2⌋ |
| Theorem 3.1 | Rigid words with a tight letter are conjugates of ℓ^t ℓ̄^{n−t} with t odd or t = n, or of (ℓℓ̄)^{n/2} |
| Theorem 1.1 | The words with D(w) = ⌊(n−1)/2⌋ |

The proofs are formalized in Lean 4 with Mathlib: the six main theorems, including `conjectureA` and `not_conjectureB`, depend only on the axioms propext, Classical.choice and Quot.sound. The release workflow builds the Lean project and runs the independent checks in C (every word of length n ≤ 22), C++ (every necklace, n ≤ 28), Python (from the definitions, n ≤ 12), Julia (every lemma of the proof, n ≤ 16) and Bash (n ≤ 10) before publishing.

Files:
- `SimpsonCircularAbelianSquares_final2.pdf`: the paper
- `SimpsonCircularAbelianSquares_final2-tex.zip`: LaTeX source with the figures as PNG
- `SimpsonCircularAbelianSquares_final2-arxiv.tar.gz`: the same source, ready for arXiv

The repository also holds `preprintSimpsonCircularAbelianSquares/SimpsonCircularAbelianSquares.pdf` and `MasterSimpsonCircularAbelianSquares_masterzipfinal2.zip` with every file.
