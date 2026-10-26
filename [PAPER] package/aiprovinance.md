# AI provenance

Paper: The minimum number of distinct abelian squares in a binary circular word
Author: Deep Bhattacharjee. No AI system is an author.

The original work used Claude (Anthropic) through Claude Code for the proofs, Lean formalisation, code, figures and manuscript preparation. The author's existing provenance records that role; this package does not recast the work as unaided human research.

For the 26 October 2026 amsart edition, OpenAI Codex inspected the written argument, compared the final Lean statements with the mathematical claims, recorded the successful repository verification at commit a08e1ce81c2f8c863844473f5ad56e02ac9cc212, preserved the proof body and formalisation sources, ran the supplied Python small-case verifier and an independent enumerator, and converted the manuscript to amsart. The precise fresh-check results and limits are in verification/.

The human-understanding declaration remains the existing Hexagon “some parts” declaration. No new author attestation of complete human understanding has been inferred from automated checks. The report does not claim that a new full Lean rebuild occurred locally.

The mathematical theorem covers every positive length; finite enumeration is a supporting check, not its general proof. The original even-length classification is disproved and replaced by the complete corrected list. This does not resolve the separate linear-word conjecture.
