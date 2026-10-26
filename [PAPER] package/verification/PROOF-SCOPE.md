# Proof and verification scope

The general mathematical proof is in Sections 2-4 of the manuscript. It treats every positive word length, and includes the lower bound, all equality cases and the explicit correction of the conjecture's even-length list. No unproved theorem from a preprint is used as a mathematical input; Simpson's preprint supplies the conjecture being answered, and the other research references give context.

Definitions were compared with Circ/Statement.lean: factors have length at most n, distinctness is by the actual word, an abelian square has nonempty halves with equal letter counts, and conjugacy is cyclic rotation. The final statements in Circ/Simpson.lean prove min_distinct, extremal_odd, extremal_even, conjectureA, not_conjectureB and counterexample. This covers the general theorem, not only a bounded search.

The prior successful verify run is recorded in previous-ci.json at the source commit in source-identity.json. The Lean and checking source files were compared with Git blob hashes and retained. This package does not claim a fresh local full Lean rebuild. Any fresh release CI must be distinguished from that earlier evidence.

The fresh Python checks are in local-check.json and local-check.log. They support the proof but do not establish the result for arbitrary n. This paper resolves the stated circular-word problem with the corrected classification; it does not resolve the separate linear-word minimum conjecture or all problems in Simpson's survey. Novelty searches are not a proof that no earlier work exists, and no journal acceptance is asserted.
