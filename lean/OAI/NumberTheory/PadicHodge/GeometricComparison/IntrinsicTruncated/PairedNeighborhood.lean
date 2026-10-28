import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedParameters
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PointedRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.TraceBasisRestriction

/-! # Paired Neighborhood -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The final paired projective chart determines an exact source
neighborhood for the same original pointed frame. Every smaller affine
source open has its native frame target inside that final chart. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra
variable
  {U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

def Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv := IntegralComparison.TruncatedModel.PointedLocalEquiv.equiv
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains

def Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood : (A.truncatedShiftModel n m hm).left.Opens :=
  IntegralComparison.AffineSection.EquivNeighborhood.Geometry.sourceFor
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    P.source.val P.target.val P.source.property P.target.property (Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv P)
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient)

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood_below : Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P ≤ P.source.val :=
  IntegralComparison.AffineSection.EquivNeighborhood.Geometry.sourceFor_below
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    P.source.val P.target.val P.source.property P.target.property (Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv P)
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient)

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood_contains :
    ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P :=
  IntegralComparison.AffineSection.EquivNeighborhood.Geometry.sourceFor_contains
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    P.source.val P.target.val P.source.property P.target.property (Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv P)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedIdentitySection n)
    ((top_unique P.source_contains).trans (top_unique P.target_contains).symm)
    (IntegralComparison.TruncatedModel.PointedSquares.section_square
      q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains)
    P.source_contains ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient)
    P.paired.original.contains

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.final_good
    (hgood : IntegralComparison.FiniteEtale.TraceBasis.Good (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
      ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U)) :
    IntegralComparison.FiniteEtale.TraceBasis.Good (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
      ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient) := by
  let : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
  let : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left :=
    A.truncatedShiftMap_etale n m hm
  exact IntegralComparison.FiniteEtale.TraceBasisRestriction.good (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U)
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient) hgood
    (P.paired.affine.preimage (A.truncatedTraceMorphism n).left)
    ((A.truncatedTraceMorphism n).left.preimage_mono P.paired.below)

variable (V : (A.truncatedShiftModel n m hm).left.affineOpens)
  (hV : V.val ≤ Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P)

include hV in
theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source : V.val ≤ P.source.val := hV.trans (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood_below P)

def Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget := IntegralComparison.TruncatedModel.PointedRestriction.target
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV)

def Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedEquiv := IntegralComparison.TruncatedModel.PointedRestriction.equiv
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV)

def Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso := IntegralComparison.TruncatedModel.PointedRestriction.frameIso
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV)

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedReduction :
    (A.truncatedShiftReduction n m hm) ⁻¹ᵁ V.val =
      (A.truncatedReduction n) ⁻¹ᵁ (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).val :=
  IntegralComparison.TruncatedModel.PointedRestriction.reduction
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV)

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below : (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).val ≤
    (A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient :=
  IntegralComparison.AffineSection.EquivNeighborhood.Geometry.target_below_of_sourceFor
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    P.source.val P.target.val P.source.property P.target.property (Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv P)
    V.val ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient) hV

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains (hcontains : ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ V.val) :
    ⊤ ≤ (A.truncatedIdentitySection n) ⁻¹ᵁ (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).val :=
  IntegralComparison.TruncatedModel.PointedRestriction.target_contains
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV) hcontains

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso_ambient (a : Γ((A.truncatedShiftModel n m hm).left, V.val)) :
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso P V hV).hom.ambientMap a = Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedEquiv P V hV a :=
  IntegralComparison.TruncatedModel.PointedRestriction.frameIso_ambient
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    P.source P.target P.reduction
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (A.truncatedIdentitySection n) (A.truncatedIdentitySection_over n)
    A.specialIdentitySection A.specialIdentitySection_over
    (A.truncatedShiftIdentitySection_reduction n m hm).symm (A.truncatedIdentitySection_reduction n)
    P.source_contains P.target_contains
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV) a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
