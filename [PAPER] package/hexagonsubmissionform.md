# Hexagon replacement submission: Paper 15

Existing record: https://hexagonmath.org/2610.00473v1

Use the record's replacement/version workflow. The new identifier is not assigned yet; do not present 2610.00473v2 as published until Hexagon confirms it.

## Title
The minimum number of distinct abelian squares in a binary circular word

## Abstract
We prove that every binary circular word of length $n$ contains at least $\lfloor(n-1)/2\rfloor$ distinct abelian squares, and we determine all words attaining this bound. This settles Simpson's circular-word problem: the odd-length assertion holds, while the even-length extremal list must also include $(ab)^{n/2}$ when $n\equiv2\pmod4$ and $n\ge6$.

## Subjects and indexing
- Primary: math.CO - Combinatorics
- Cross-lists: cs.DM - Discrete Mathematics; cs.FL - Formal Languages and Automata Theory
- Tags: abelian square, binary circular word, extremal classification, Parikh vector, formal verification
- MSC2020: 68R15 (primary); 05A05; 68V15
- arXiv identifier: leave blank; the author's manuscript is not on arXiv.

## Contributor
Deep Bhattacharjee, sole author and submitting contributor. ORCID 0000-0003-0466-750X. Affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India. Email: itsdeep@live.com.

The current GitHub manuscript and published Hexagon v1 list Deep Bhattacharjee alone. This edition preserves that authorship; it does not use the superseded two-author local draft.

## Required declarations
- Text: A mix of human-written and AI-generated.
- Human understanding: Some parts of this contribution, but not all, have been checked and understood by a human. This retains the published v1 declaration. The author may change it only if a different declaration is now accurate.
- Provenance: The original proof, Lean formalisation, figures and checking code were developed with Claude (Anthropic), under the author's direction. OpenAI Codex assisted with this edition's source audit, independent small-case checking and conversion to amsart. The mathematical proof body is unchanged from the pinned repository source. Both tools are disclosed; neither is an author.
- Tools: Claude Code; OpenAI Codex; Lean 4.34.1 with Mathlib; Python; C; C++; Julia; shell; TeX Live.
- Formalisation link: https://github.com/creelie/literate-octo-lamp/blob/main/verification/lean/Circ/Simpson.lean
- AI provenance file: aiprovinance.md
- License for the Hexagon manuscript: CC BY 4.0, as on the existing Hexagon record. Formalisation/checking code retains its repository license and is linked separately.

## Upload files
- Source: SimpsonCircularAbelianSquarestex.zip. Its root contains main.tex and figures/; choose main.tex as the main document. Compiler: pdfLaTeX. No BibTeX or shell escape is needed.
- Preview PDF: SimpsonCircularAbelianSquares.pdf.
- No Lean files belong in the Hexagon TeX ZIP. Use the formalisation link above.
- No other paper or external preprint PDF is embedded in this manuscript.
- Changes for this version: amsart layout, portable source root, explicit source/verification record and refreshed submission metadata. The general theorem and its proof are retained.
