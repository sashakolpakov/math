import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedNeighborhood
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineSection.EquivPullbackRestriction

/-! # Paired Parameter Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison

noncomputable section

/-! The restricted original pointed frame sends the finite pullback
of each final original parameter to the corresponding final transported
parameter, with every source and target restriction retained. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
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

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.original_parameters (j : Fin A.dimension) :
    (A.truncatedTraceMorphism n).left.app P.paired.ambient (P.paired.original.parameters j) =
      (A.truncatedModel n).scheme.left.presheaf.map
        (homOfLE ((A.truncatedTraceMorphism n).left.preimage_mono P.paired.below)).op
          ((A.truncatedTraceMorphism n).left.app U (D.parameters j)) := by
  rw [P.paired.original_parameters j]
  exact ConcreteCategory.congr_hom
    ((A.truncatedTraceMorphism n).left.naturality (homOfLE P.paired.below).op) (D.parameters j)

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.transported_parameters (j : Fin A.dimension) :
    (A.truncatedTraceMorphism n).left.app P.paired.ambient (P.paired.transported.parameters j) =
      (A.truncatedModel n).scheme.left.presheaf.map (homOfLE P.paired.source_below).op
        (Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv P ((A.truncatedShiftMap n m hm).appLE
          ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) P.source.val P.source_below
          ((A.truncatedTraceMorphism n).left.app U (D.parameters j)))) :=
  P.paired.transported_parameters j

variable (V : (A.truncatedShiftModel n m hm).left.affineOpens)
  (hV : V.val ≤ Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P)
  (hVW : V.val ≤ (A.truncatedShiftMap n m hm) ⁻¹ᵁ
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient))

theorem Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso_parameters (j : Fin A.dimension) :
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso P V hV).hom.ambientMap
      ((A.truncatedShiftMap n m hm).appLE
        ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient) V.val hVW
        ((A.truncatedTraceMorphism n).left.app P.paired.ambient (P.paired.original.parameters j))) =
    (A.truncatedModel n).scheme.left.presheaf.map (homOfLE (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV)).op
      ((A.truncatedTraceMorphism n).left.app P.paired.ambient (P.paired.transported.parameters j)) := by
  rw [Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso_ambient, Geometry.AbelianH1Model.TruncatedPairedPointParameters.original_parameters, Geometry.AbelianH1Model.TruncatedPairedPointParameters.transported_parameters]
  exact IntegralComparison.AffineSection.EquivPullbackRestriction.Geometry.pullback_restriction
    (IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    (A.truncatedShiftOver n m hm) P.source.val P.target.val
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) P.source.property P.target.property
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.originalEquiv P) P.source_below V.val (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affine_below_source P V hV)
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient)
    ((A.truncatedTraceMorphism n).left.preimage_mono P.paired.below)
    P.paired.source_below hVW (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV)
    ((A.truncatedTraceMorphism n).left.app U (D.parameters j))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison
