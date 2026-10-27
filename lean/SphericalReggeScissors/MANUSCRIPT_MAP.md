# Manuscript-to-Lean map

This file records the trust boundary declaration by declaration. “Checked”
means Lean proves the stated implication from definitions or structure
fields. “Conditional” means Lean proves the implication from a named
external-package field. “External” means that the mathematical construction
or theorem is not formalized here.

No row should be read as saying that an informal interpretation of a carrier
type has been constructed merely because the carrier occurs in Lean.

## External package

| Manuscript input | Lean representation | Status |
|---|---|---|
| E1: geometric Regge theorem | **GeometricReggeInputs**, **physical_regge_pair_realized**, **geometric_angle_length_action_certified**, and **ProofContract.regge_volume**; the angle/length consequence also enters **split_formula_reggeMate** | External facts, conditional use |
| E2: relative framed quadric coefficients | **MotivicInputs.RelativeObject**, **coefficient**, **isAlternatingFaceObject**; the two object witnesses and coefficient comparisons in **ProofContract** | External construction |
| E3: exact graded pieces and strict heart | **hasExactThreeGradedPieces**, **strict_three_weight_heart_constructed** and the two object certificates in **ProofContract** | External construction/comparison |
| E3: primitive \(=\) endpoint extension | **MotivicInputs.primitiveComparison** | External comparison |
| E3: \(H^1(U,\mathbf Q(2))=0\) | **MotivicInputs.h1_vanishes** | External Garkusha--Borel application |
| E4: relative six-channel formula | **CoproductBridge.split_formula_original**, **split_formula_reggeMate** | External comparison |
| E4: finite-etale/sign-Artin descent | **CoproductBridge.splitPullback**, **finite_etale_sign_trace_injective** | External comparison |
| E4: algebraization of real length/angle relations | **movingLeft**, **movingRight**, and **split_formula_reggeMate** | External density/cofactor bridge; tensor equality then checked |
| E4: coproduct-compatible specialization | **SpecializationInputs.middleSpecialize**, **quadricCoproduct**, **ProofContract.quadric_coproduct_specialization** | External commuting square; fibre primitivity derived in Lean |
| E5: specialization | **SpecializationInputs.specialize**, **endpoint** | External construction |
| E5: fibre endpoint equals \(c_G\) | **ProofContract.fibre_endpoint_eq_cG** | External comparison |
| E6: Goncharov \(c_G\) and injectivity | **SpecializationInputs.goncharov**, **goncharov_injective** | External theorem |
| E6: projective duality | **SpecializationInputs.duality**, **duality_involutive**, **ProofContract.duality_comparison** | External theorem/comparison; injectivity derived internally |
| E6: spherical-to-quadric injection | **SpecializationInputs.spherical**, **spherical_injective** | External theorem |
| E7: geometric/Goncharov presentation comparison | **ProofContract.presentationComparison**, **presentation_defect_comparison** | External theorem/comparison |
| E8: suspension exactness | **ScissorsInputs.reduction**, **suspension**, **exact_at_full** | External theorem |
| E8: rationalization | **ScissorsInputs.rationalize**, **rationalization_injective** | External typed consequence of unique divisibility |
| E8: area and suspension volume | **ScissorsInputs.area**, **area_injective**, **suspension_volume** | External theorem plus stated geometric formula |
| E8: cancellation to equidecomposition | **ScissorsInputs.cancellation**, **FiniteEquidecomposition** | External theorem returning a typed finite-list witness |

The exact graded pieces
\(\mathbf Q(0),\mathbf Q(1)^5\oplus\chi(1),\mathbf Q(2)\), existence of a
strict three-weight heart, construction of the relative face objects, and
compatibility of their frames are represented by separately named contract
certificates for E2--E4. They are not constructed by Lean or by ordinary
vector-space homology.

### Exhaustive field closure

The table above names the mathematical maps. The following rows name the
remaining selectors, witnesses, and glue equalities so that no hypothesis can
be added to the Lean contract without being assigned to E1--E8:

| Input | Remaining Lean fields |
|---|---|
| E1 | **GeometricReggeInputs.isNondegeneratePhysicalReggePair**, **GeometricReggeInputs.hasGeometricAngleAndLengthAction**; **ProofContract.original**, **reggeMate**, **geometry** |
| E2 | **MotivicInputs.coproduct**; **CoproductBridge.relativeOriginal**, **relativeReggeMate**; **ProofContract.relativeOriginalObject**, **relativeReggeMateObject**, **original_face_object_constructed**, **reggeMate_face_object_constructed**, **relative_original_coefficient**, **relative_reggeMate_coefficient**, **universalDefect**, **universal_defect_is_difference** |
| E3 | **MotivicInputs.strictThreeWeightHeart**; **ProofContract.original_exact_three_graded_pieces**, **reggeMate_exact_three_graded_pieces** |
| E4 | **CoproductBridge.fixedLeft₀**, **fixedLeft₁**, **fixedRight₀**, **fixedRight₁**; **SpecializationInputs.middleSpecialize**, **quadricCoproduct**; **ProofContract.quadricDualDefect**, **quadric_coproduct_specialization** |
| E6 | **ProofContract.goncharovSphericalDefect** |
| E7 | **ProofContract.reducedRationalDefect** |
| E8 | **ScissorsInputs.rationalize**, **rationalization_injective**, **volume**, **scissorsClass**, **decomposes**, **pieceIsometric**; **ProofContract.reducedDefect**, **rationalization_comparison**, **reduced_comparison** |
| Package selectors | **ProofContract.motivic** (E2--E3), **coproductBridge** (E4), **specialization** (E4--E6), and **scissors** (E8) |

The machine-readable ownership is **contract_map.json**.
**scripts/check_contract_parity.py** parses every field of the six trust
structures in **ExternalInputs.lean**, requires exact coverage by that file,
and checks that all eight numbered manuscript inputs exist.

## Section 1: statement and route

| Manuscript item | Lean declaration | Status |
|---|---|---|
| **cp:thm-main**, conditional spherical Regge scissors theorem | **spherical_regge_scissors** and **spherical_regge_equidecomposable** | Checked from **ProofContract** |
| Universal framed defect vanishes | **contract_universal_defect_zero** | Checked from the motivic and coproduct packages |
| Fibre primitivity | **contract_universal_coproduct_zero**, **contract_quadric_dual_defect_is_primitive** | Checked directly from E4, independently of E3 |
| Reduced and full defects vanish | **contract_reduced_defect_zero**, **contract_full_defect_zero** | Checked |
| Contract is not contradictory | **finiteContract_exists** | Checked finite model |
| Regge involution plus equal volume is insufficient | **equal_volume_does_not_force_scissors_class** | Checked countermodel |

## Section 2: phase and orientation algebra

| Manuscript item | Lean declaration | Status |
|---|---|---|
| **cp:def-angle-gram**, angle Gram matrix | no geometric tetrahedron structure is modeled; Laurent entry is **gramEntry** | Definition only / external geometry |
| **cp:lem-regge-matrix**, \(R^t=R\), \(R^2=I\), eigenspaces | **reggeMatrix_transpose**, **reggeMatrix_mul_self**, **reggeMatrix_orthogonal**, **reggeMatrix_mulVec_const**, **reggeMatrix_mulVec_of_sum_eq_zero** | Checked |
| **cp:thm-regge-input**, geometric Regge input | E1 above; **GeometricReggeInputs**, **ProofContract.regge_volume**, and the Regge channel data | External |
| **cp:lem-algebraic-regge-involution**, monomial Regge automorphism | **reggePhase_product**, **PhasePoint.regge**, **PhasePoint.regge_involutive** | Checked |
| Laurent product-to-sum identity | **phase_product_to_sum**, **gramEntry_inv** | Checked |
| Equation \(1-y^2=-s^2\) | **qGram_qSkew_relation** | Checked |
| **cp:lem-determinant-quadratic**, determinant quadratic and coefficient invariance | **gramMatrix_det**, **gramMatrix_det_quadratic**, **determinantB_regge_invariant**, **determinantC_regge_invariant** | Checked |
| **cp:lem-rational-charts**, minus and plus rational charts | **minus_chart_linearization**, **minus_chart_reconstruct**, **minus_chart_formula**, **plus_chart_linearization**, **plus_chart_reconstruct**, **plus_chart_formula** | Mixed: coordinate algebra checked; scheme packaging external |
| Coverage on \(sw\ne0\) | **both_chart_denominators_force_four_sw**, **chart_cover** | Checked |
| **cp:def-U**, universal principal open and its function field | no scheme-level declaration | Definition / external algebraic-geometry packaging |
| **cp:prop-physical-point-on-chart**, a physical pair lies on a chart | no model of positive spherical tetrahedra; represented by the external proof contract for the chosen pair | External geometric bridge |
| **cp:prop-fixed-p-cover**, fixed phase | **fixedPhasePolynomial**, **fixedPhase_discriminant**, **fixedPhase_inv_eq_deck**, **fixedPhase_deck_involutive**, **fixedPhase_deck_preserves_root**, **fixedPhase_root_times_deck** | Mixed: coordinate algebra checked; finite-etaleness external |
| Finite-etaleness of the fixed-phase cover | no scheme-level declaration | External algebraic geometry |

## Section 3: motivic dictionary

| Manuscript item | Lean declaration | Status |
|---|---|---|
| **cp:def-face-motive**, intended relative face motive | E2; no motive type is defined | External construction/specification |
| Three graded pieces and strict filtration | **hasExactThreeGradedPieces**, **strict_three_weight_heart_constructed** | Explicit external certificates |
| **cp:def-coefficient-contract**, weight-two coefficient contract | **MotivicInputs**, **CoproductBridge**, **SpecializationInputs** | Explicit interface |
| **cp:lem-three-level-framed**, primitive vanishing | **primitive_eq_zero** | Checked |
| Equality from equal coproducts | **eq_of_coproduct_eq** | Checked |
| \(H^1(U,\mathbf Q(2))=0\) route | **MotivicInputs.h1_vanishes** | External |

## Section 4: universal defect

| Manuscript item | Lean declaration | Status |
|---|---|---|
| **cp:lem-split-strata**, coordinate-stratum calculation | **phase_vector_isotropic**, **alternating_mul_symmetric_square**, **alternating_mul_symmetric_skew_adjoint**, **normalizedBinaryInvolution_square**, **qGram_qSkew_relation**, and the fixed-phase declarations check its binary algebra | Mixed: binary algebra checked; global family regularity external |
| **cp:prop-weight-calculation**, external three-weight package | **MotivicInputs.primitiveComparison**, **h1_vanishes** | External |
| Cross-ratio \(e^{2i\phi}\) and geometric channel identification | **CoproductBridge.split_formula_original**, **split_formula_reggeMate** | External analytic/geometric identification |
| Equation \(H^tH=4I\) | **hadamardMatrix_eq_two_smul**, **hadamardMatrix_orthogonal** | Checked |
| **cp:lem-regge-tensor-cancellation**, four-channel tensor cancellation | **hadamard_bilinear_cancellation**, **hadamard_tensor_cancellation**, **regge_bilinear_cancellation**, **regge_tensor_cancellation**, **six_channel_tensor_invariance** | Checked |
| **cp:lem-coproduct-zero**, middle coproduct vanishes and fibre is primitive | **six_channel_tensor_invariance**, **coproduct_eq_of_six_channel_calculation**, **coproduct_of_regge_difference_eq_zero**, **contract_quadric_dual_defect_is_primitive** | Checked from E4 |
| **cp:thm-relative-defect-zero**, universal defect vanishes | **universal_framed_defect_vanishes**, **contract_universal_defect_zero** | Checked from E2--E4 |

## Section 5: specialization and scissors

| Manuscript item | Lean declaration | Status |
|---|---|---|
| **cp:thm-goncharov-weight-two**, Goncharov weight-two injection | **SpecializationInputs.goncharov**, **goncharov_injective** | External |
| **cp:lem-spherical-presentations**, spherical presentation and injection | **ProofContract.presentationComparison**, **presentation_defect_comparison**, **SpecializationInputs.spherical**, **spherical_injective** | External |
| **cp:lem-fibre-comparison**, fibre endpoint comparison | **ProofContract.fibre_endpoint_eq_cG** | External |
| **cp:prop-reduced-scissors-zero**, reduced defect vanishes | **goncharov_spherical_defect_vanishes**, **reduced_rational_defect_vanishes_of_presentation**, **integral_reduced_defect_vanishes**, **contract_reduced_defect_zero** | Checked diagram chase |
| Equal volume kills volume defect | **volume_defect_vanishes** | Checked |
| Suspension, area, and full defect | **full_defect_vanishes**, **contract_full_defect_zero** | Checked from E8 |
| Equality gives equidecomposition | **equidecomposable_of_full_defect_zero** | Checked from cancellation input; returns **Nonempty FiniteEquidecomposition** |
| Final theorem | **spherical_regge_scissors** | Checked from complete contract; returns a typed finite-list certificate |

## Scope conclusion

The Lean development verifies the conditional logic and the listed finite
algebra. It does not prove that a geometric Regge pair supplies a
**ProofContract**. The unresolved mathematical work is exactly the
relative-motivic and comparison package named in E2--E5, together with any
row above explicitly marked external or not machine checked.
