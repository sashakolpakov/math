# Manuscript and Lean declarations

The target is `StickKnots.lean`, built with the checked-in Lean 4.32.0 and
mathlib revision `81a5d257c8e410db227a6665ed08f64fea08e997`.
Run `make verify` in this directory. The source and axiom checker compiles
every declaration listed in the public entry point and rejects proof escapes
and dependencies beyond the three documented Lean/mathlib foundations.

| Manuscript argument | Lean location and principal declarations | Boundary |
|---|---|---|
| Cubic and quartic intersection walls | `Geometry.lean`: `segment_intersection_implies_det_wall`, `adjacent_improper_intersection_implies_crossSq_wall`; `PolygonalCore.lean`: `Config.wallFree_embedded` | Internal coordinate geometry is proved. |
| Actual polynomial family and its degrees | `PolygonalCore.lean`: `Config.wallFree_iff_forall_indexedWallPolynomial_ne_zero`, `Config.indexedWallPolynomial` | Polynomials are actual `MvPolynomial` objects. |
| Classifying path components | `CertificationLogic.lean`: `PathClassificationCertificate.onPathComponents_surjective`, `natCard_class_le_pathComponents` | Path invariance and generic support of classical knot types are external. |
| Stick-knot upper theorem | `StickUpperCertificate.lean`: `boundedStickKnot_count_le_unsliced`; `Counting.lean`: `weighted_partial_choose_le` | Barone–Basu is a uniform theorem hypothesis about degree-four families. Lean proves the entropy/binomial estimate and its composition with topology. |
| Baseline arc-index lower arithmetic | `Counting.lean`, `FewnomialBound.lean` | Historical numerical wrappers are auxiliary; the main target uses the actual bounded-stick subtype. |
| Doubly down–up quarter-family | `DoublyAlternating.lean`: `factorial_fourth_power_le_card_doublyDownUp` | Construction, injectivity, both descent sets, factorial comparison, and logarithmic loss are internal. |
| Short pure braids | `LowerCertification.lean`: `GarsideStageCertificate.purify_injective`, `purify_factorLength`, `exists_endpointFiber_ceil_lower` | Garside uniqueness, endpoint multiplication and cancellation are external structural facts. Pigeonholing and endpoint correction are proved. |
| Finite prime-satellite lower theorem | `LowerCertification.lean`: `KnotTransferCertificate.finite_stick_lower_bound_full_language`, `finite_stick_lower_bound` | Malyutin–Stupakov, Huh–Oh and orientation reversal are external. Fiber counting and stick budgets are proved. |
| Combining both sides on one knot population | `AsymptoticCertificate.lean`: `certifiedKnotCount_finite_lower_at`, `certifiedKnotCount_finite_upper` | Finiteness follows from the upper certificate. The lower count is transported into the same subtype. |
| Logarithmic growth order | `AsymptoticCertificate.lean`: `certifiedKnotCount_log_isTheta` | All remaining analysis is internal. |
| Refined lower coefficient | `AsymptoticCertificate.lean`: `eventually_coefficient_lower_bound_fixedWord` | Every `c < 2/3` is proved eventually valid, with no arithmetic hypothesis. |
| Refined upper coefficient | `ManuscriptArithmetic.lean`: `unslicedUpperLog_le_three_scale_add_linear`, `eventually_coefficient_upper_bound` | Every `c > 3` is proved eventually valid. |
| Explicit optimized second-order deficit | `ManuscriptArithmetic.lean`: `optimizedStirlingLowerLog_deficit_of_size`, `provedOptimizedDeficitArithmetic`, `eventually_optimized_deficit_lower_bound_proved` | The formerly external floor/log interface is discharged by a Lean proof. The pointwise arithmetic constant is 100; only an unspecified `O(N)` is needed in the paper. |
| Stiefel normalization and positive measure | Manuscript support theorem | Outside the Lean target; also unnecessary for the unsliced upper bound. |
| Links and parity addressing | Manuscript addressed-linking proposition and link theorems | Outside the Lean target. The corpus audit reviews the written construction separately. |
| Strong-geometry priority comparison and fewnomial questions | Manuscript introduction and final section | Literature comparison and research directions, not Lean theorem claims. |

The development does not construct the classical ambient-isotopy quotient or
prove the cited external theorems. A small axiom list does not remove theorem
hypotheses. The main arithmetic and finite combinatorial deductions are
kernel checked relative to the named external interfaces.
