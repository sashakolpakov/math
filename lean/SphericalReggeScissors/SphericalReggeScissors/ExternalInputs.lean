/-
Discussions and model prompting: Alexander Kolpakov (UATX).

Source: sashakolpakov/spherical-regge-scissors, commit
d40eb8990bcf1ba5525435f8517e9ba5c202b549.
-/

import SphericalReggeScissors.CoproductAlgebra

/-!
# The external theorem contract

The manuscript uses deep theorems about relative motives, motivic
cohomology, Goncharov's quadric complex, and spherical scissors groups.
This file gives those results an explicit Lean boundary.  In particular,
none of them is installed as a global axiom: a caller must supply a value
of the relevant structure.

Motivic, fibrewise, and rationalized carrier types are explicitly rational
modules and their comparison maps are linear.  The integral spherical
scissors carriers `Plane`, `Full`, and `Reduced` remain additive groups.
-/

namespace SphericalReggeScissors

open scoped TensorProduct

universe uU uM uL uA uH uF uQ uQM uK uP uS uR uRQ uG uT uPiece

/--
The relative-object and three-weight inputs behind the slogan "primitive
equals an extension".  The face-complex, graded-piece, and strict-heart
certificates are deliberately separate: an implementation of motives must
discharge all three rather than treating them as one opaque comparison.

* `primitiveComparison` is the comparison between the kernel of the
  reduced middle coproduct and the endpoint `H¹(U,ℚ(2))` group.
* `h1_vanishes` packages the Garkusha--Borel computation that this
  endpoint group is zero on the universal rational base.

The reduced coproduct itself is part of the data because its explicit
Regge invariance is proved inside the manuscript rather than assumed here.
-/
structure MotivicInputs
    (Universal : Type uU) (Middle : Type uM) (H1 : Type uH)
    [AddCommGroup Universal] [Module ℚ Universal]
    [AddCommGroup Middle] [Module ℚ Middle]
    [AddCommGroup H1] [Module ℚ H1] where
  /-- Abstract carrier for the actual alternating-face objects. -/
  RelativeObject : Type uU
  /-- The framed coefficient represented by a relative face object. -/
  coefficient : RelativeObject → Universal
  /-- Interpretation obligation for the four-term alternating face construction.
  This abstract predicate is supplied by an intended model; Lean does not define
  relative motives merely from its presence. -/
  isAlternatingFaceObject : RelativeObject → Prop
  /-- Interpretation obligation for the exact `0,1,2` graded-piece calculation. -/
  hasExactThreeGradedPieces : RelativeObject → Prop
  /-- Interpretation obligation asserting that the required strict heart exists. -/
  strictThreeWeightHeart : Prop
  strict_three_weight_heart_constructed : strictThreeWeightHeart
  coproduct : Universal →ₗ[ℚ] Middle
  /-- The actual hypothesis used by the primitive argument.  The abstract
  object predicates above do not by themselves construct this comparison. -/
  primitiveComparison : coproduct.ker ≃ₗ[ℚ] H1
  h1_vanishes : ∀ h : H1, h = 0

/--
The narrow bridge from the two relative framed objects to the explicit
middle-coproduct calculation.

`splitPullback` is pullback to the splitting cover of the nonsplit face.
Its injectivity is named `finite_etale_sign_trace_injective` because the
manuscript proves it with the finite-étale trace/norm.  The two formula
fields identify the motivic coproducts with the six coordinate channels:
two fixed and four moving.  The mate formula is forced to use the actual
`reggeTransform`; consequently equality of the two expressions follows
from `six_channel_tensor_invariance` and is a theorem, not an input field.
-/
structure CoproductBridge
    (Universal Middle LeftFactor RightFactor : Type*)
    [AddCommGroup Universal] [Module ℚ Universal]
    [AddCommGroup Middle] [Module ℚ Middle]
    [AddCommGroup LeftFactor] [Module ℚ LeftFactor]
    [AddCommGroup RightFactor] [Module ℚ RightFactor]
    (coproduct : Universal →ₗ[ℚ] Middle) where
  relativeOriginal : Universal
  relativeReggeMate : Universal
  splitPullback : Middle →ₗ[ℚ] TensorProduct ℚ LeftFactor RightFactor
  finite_etale_sign_trace_injective : Function.Injective splitPullback
  movingLeft : Four → LeftFactor
  movingRight : Four → RightFactor
  fixedLeft₀ : LeftFactor
  fixedLeft₁ : LeftFactor
  fixedRight₀ : RightFactor
  fixedRight₁ : RightFactor
  split_formula_original :
    splitPullback (coproduct relativeOriginal) =
      fixedLeft₀ ⊗ₜ[ℚ] fixedRight₀ + fixedLeft₁ ⊗ₜ[ℚ] fixedRight₁ +
        ∑ i, movingLeft i ⊗ₜ[ℚ] movingRight i
  split_formula_reggeMate :
    splitPullback (coproduct relativeReggeMate) =
      fixedLeft₀ ⊗ₜ[ℚ] fixedRight₀ + fixedLeft₁ ⊗ₜ[ℚ] fixedRight₁ +
        ∑ i, reggeTransform movingLeft i ⊗ₜ[ℚ] reggeTransform movingRight i

/--
External comparison maps used after specializing the universal identity to
a complex point.

`specialize` and `endpoint` keep the fibre operation visible instead of
silently identifying a relative framed coefficient with a `K₃` class.
`quadricCoproduct` is the field-level reduced coproduct and `goncharov` is
`c_G` on its kernel only.  `middleSpecialize` lets the proof derive fibre
primitivity from a commuting coproduct square rather than assuming it.
This typing matters: `c_G` is not a map on arbitrary quadric generators. `duality` is
projective duality; and `spherical` is Goncharov's injection from his
spherical presentation into all quadric classes.  The separate E7
presentation isomorphism is stored in `ProofContract`.
Projective duality is recorded as an involution, from which its
injectivity is proved internally; the other two injectivity statements
are precisely Goncharov's cancellation steps.
-/
structure SpecializationInputs
    (Universal Middle Fibre Quadric QuadricMiddle K3 SphericalPresentation : Type*)
    [AddCommGroup Universal] [Module ℚ Universal]
    [AddCommGroup Middle] [Module ℚ Middle]
    [AddCommGroup Fibre] [Module ℚ Fibre]
    [AddCommGroup Quadric] [Module ℚ Quadric]
    [AddCommGroup QuadricMiddle] [Module ℚ QuadricMiddle]
    [AddCommGroup K3] [Module ℚ K3]
    [AddCommGroup SphericalPresentation] [Module ℚ SphericalPresentation] where
  specialize : Universal →ₗ[ℚ] Fibre
  endpoint : Fibre →ₗ[ℚ] K3
  middleSpecialize : Middle →ₗ[ℚ] QuadricMiddle
  quadricCoproduct : Quadric →ₗ[ℚ] QuadricMiddle
  goncharov : quadricCoproduct.ker →ₗ[ℚ] K3
  duality : Quadric →ₗ[ℚ] Quadric
  spherical : SphericalPresentation →ₗ[ℚ] Quadric
  goncharov_injective : Function.Injective goncharov
  duality_involutive : Function.Involutive duality
  spherical_injective : Function.Injective spherical

/-- A concrete finite-equidecomposition certificate.  Its two lists are
finite by construction; an intended geometric model supplies the meanings
of `decomposes` and `pieceIsometric`. -/
structure FiniteEquidecomposition
    (Tetrahedron : Type uT) (Piece : Type uPiece)
    (decomposes : Tetrahedron → List Piece → Prop)
    (pieceIsometric : Piece → Piece → Prop)
    (left right : Tetrahedron) where
  leftPieces : List Piece
  rightPieces : List Piece
  left_decomposition : decomposes left leftPieces
  right_decomposition : decomposes right rightPieces
  pairwise_isometric : List.Forall₂ pieceIsometric leftPieces rightPieces

/-!
The standard scissors-theoretic statements used to pass from the reduced
class back to a finite-equidecomposition certificate.

`exact_at_full` says that the kernel of reduction is the image of
spherical suspension.  `rationalize` keeps the manuscript's passage to
`Pred(S³) ⊗ ℚ` explicit, and its injectivity records the consequence of
unique divisibility.  `suspension_volume` records
`Vol (Σq) = (π/2) Area(q)`.  `area_injective` is the classification of
spherical polygon scissors classes by area.  Finally, `cancellation` is
the Zylev--Gerling passage from equality in the scissors group to a finite
spherical equidecomposition.
-/
structure ScissorsInputs
    (Plane Full Reduced ReducedRational Tetrahedron Piece : Type*)
    [AddCommGroup Plane] [AddCommGroup Full] [AddCommGroup Reduced]
    [AddCommGroup ReducedRational] [Module ℚ ReducedRational] where
  suspension : Plane →+ Full
  reduction : Full →+ Reduced
  rationalize : Reduced →+ ReducedRational
  rationalization_injective : Function.Injective rationalize
  exact_at_full : ∀ z : Full, reduction z = 0 → ∃ q : Plane, suspension q = z
  area : Plane →+ ℝ
  volume : Full →+ ℝ
  suspension_volume : ∀ q : Plane,
    volume (suspension q) = (Real.pi / 2) * area q
  area_injective : Function.Injective area
  scissorsClass : Tetrahedron → Full
  /-- Interpretation obligation saying that a finite piece list decomposes
  the indicated tetrahedron. -/
  decomposes : Tetrahedron → List Piece → Prop
  /-- Interpretation obligation for isometry of individual pieces. -/
  pieceIsometric : Piece → Piece → Prop
  cancellation : ∀ {x y : Tetrahedron},
    scissorsClass x = scissorsClass y →
      Nonempty (FiniteEquidecomposition Tetrahedron Piece
        decomposes pieceIsometric x y)

/-- Named E1 interpretation obligations for the geometric input.  These
predicates are supplied by a model and are not definitions of spherical
tetrahedra inside Lean.  Their two concrete consequences used by the proof
are not hidden in these propositions:
the angle action appears literally as `reggeTransform` in
`CoproductBridge.split_formula_reggeMate`, and volume preservation is the
`ProofContract.regge_volume` equality. -/
structure GeometricReggeInputs (Tetrahedron : Type*) where
  isNondegeneratePhysicalReggePair : Tetrahedron → Tetrahedron → Prop
  hasGeometricAngleAndLengthAction : Tetrahedron → Tetrahedron → Prop

/--
The complete, explicit proof contract for one spherical Regge pair.

The fields ending in `_comparison` are the compatibility squares that
must be checked when geometric objects are translated between the
relative-motivic, fibrewise-quadric, and spherical-scissors languages.
Keeping them as named fields prevents a Lean proof from silently replacing
one realization by another.
-/
structure ProofContract
    (Universal Middle LeftFactor RightFactor H1 Fibre Quadric QuadricMiddle K3
      Plane Full Reduced ReducedRational SphericalPresentation Tetrahedron
      Piece : Type*)
    [AddCommGroup Universal] [Module ℚ Universal]
    [AddCommGroup Middle] [Module ℚ Middle]
    [AddCommGroup LeftFactor] [Module ℚ LeftFactor]
    [AddCommGroup RightFactor] [Module ℚ RightFactor]
    [AddCommGroup H1] [Module ℚ H1]
    [AddCommGroup Fibre] [Module ℚ Fibre]
    [AddCommGroup Quadric] [Module ℚ Quadric]
    [AddCommGroup QuadricMiddle] [Module ℚ QuadricMiddle]
    [AddCommGroup K3] [Module ℚ K3]
    [AddCommGroup Plane] [AddCommGroup Full] [AddCommGroup Reduced]
    [AddCommGroup ReducedRational] [Module ℚ ReducedRational]
    [AddCommGroup SphericalPresentation] [Module ℚ SphericalPresentation] where
  motivic : MotivicInputs Universal Middle H1
  coproductBridge :
    CoproductBridge Universal Middle LeftFactor RightFactor motivic.coproduct
  relativeOriginalObject : motivic.RelativeObject
  relativeReggeMateObject : motivic.RelativeObject
  original_face_object_constructed :
    motivic.isAlternatingFaceObject relativeOriginalObject
  reggeMate_face_object_constructed :
    motivic.isAlternatingFaceObject relativeReggeMateObject
  original_exact_three_graded_pieces :
    motivic.hasExactThreeGradedPieces relativeOriginalObject
  reggeMate_exact_three_graded_pieces :
    motivic.hasExactThreeGradedPieces relativeReggeMateObject
  relative_original_coefficient :
    coproductBridge.relativeOriginal = motivic.coefficient relativeOriginalObject
  relative_reggeMate_coefficient :
    coproductBridge.relativeReggeMate = motivic.coefficient relativeReggeMateObject
  specialization :
    SpecializationInputs Universal Middle Fibre Quadric QuadricMiddle K3
      SphericalPresentation
  scissors : ScissorsInputs Plane Full Reduced ReducedRational Tetrahedron Piece
  /-- E7: Dupont's reduced group and Goncharov's presentation are not
  definitionally identified; this is their explicit comparison. -/
  presentationComparison : ReducedRational ≃ₗ[ℚ] SphericalPresentation
  original : Tetrahedron
  reggeMate : Tetrahedron
  geometry : GeometricReggeInputs Tetrahedron
  physical_regge_pair_realized :
    geometry.isNondegeneratePhysicalReggePair original reggeMate
  geometric_angle_length_action_certified :
    geometry.hasGeometricAngleAndLengthAction original reggeMate
  universalDefect : Universal
  quadricDualDefect : Quadric
  goncharovSphericalDefect : SphericalPresentation
  reducedRationalDefect : ReducedRational
  reducedDefect : Reduced
  universal_defect_is_difference :
    universalDefect =
      coproductBridge.relativeOriginal - coproductBridge.relativeReggeMate
  /-- The field-level coproduct is the specialization of the relative one.
  Fibre primitivity is derived from this square and universal coproduct
  vanishing; it is not an independent assumption. -/
  quadric_coproduct_specialization :
    specialization.quadricCoproduct quadricDualDefect =
      specialization.middleSpecialize (motivic.coproduct universalDefect)
  fibre_endpoint_eq_cG :
    ∀ hprimitive : quadricDualDefect ∈ specialization.quadricCoproduct.ker,
      specialization.goncharov ⟨quadricDualDefect, hprimitive⟩ =
        specialization.endpoint (specialization.specialize universalDefect)
  duality_comparison :
    quadricDualDefect =
      specialization.duality
        (specialization.spherical goncharovSphericalDefect)
  presentation_defect_comparison :
    goncharovSphericalDefect =
      presentationComparison reducedRationalDefect
  rationalization_comparison :
    reducedRationalDefect = scissors.rationalize reducedDefect
  reduced_comparison :
    reducedDefect =
      scissors.reduction
        (scissors.scissorsClass original - scissors.scissorsClass reggeMate)
  regge_volume :
    scissors.volume (scissors.scissorsClass original) =
      scissors.volume (scissors.scissorsClass reggeMate)

end SphericalReggeScissors
