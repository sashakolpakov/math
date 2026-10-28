import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointValueData
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedResidueScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PairedBoundedResidues
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SmoothPointValue
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointOrdinaryValueFormula
import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointFiniteValueFormula

/-! # Paired Point Values -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedPointValues.AbelianModel

noncomputable section

/-! Both actual global point values are the paired local residues with
one common scalar and the original two signs. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial _root_.HomologicalComplex
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem join_equalities {T : Sort*} {a b c d : T}
    (hab : a = b) (hcd : c = d) (hbc : b = c) : a = d :=
  hab.trans (hbc.trans hcd)

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra Geometry.AbelianH1Model.finiteSection_closed
local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.pointValuesFinite : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.pointValuesEtale : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left :=
  A.truncatedShiftMap_etale n m hm
variable
  {U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

namespace TruncatedPairedPointParameters.PointValues

section Source
variable (z : Γ((A.truncatedShiftModel n m hm).left,Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P))
  (hgood : IntegralComparison.FiniteEtale.TraceBasis.Good (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P))
  (hz : Geometry.AbelianH1Model.TruncatedPairedPointParameters.IsComponent P z)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceBelow := IntegralComparison.TruncatedModel.FinitePointValueData.nativeBelow q (ZMod q) n (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm)
    (A.truncatedShiftOver n m hm) (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
  P.paired.ambient P.paired.affine P.finiteOriginal hgood z hz
abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceCover := IntegralComparison.TruncatedModel.FinitePointValueData.nativeCover q (ZMod q) n (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm)
    (A.truncatedShiftOver n m hm) (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
  P.paired.ambient P.paired.affine P.finiteOriginal hgood z hz
abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceGlobal := IntegralComparison.TruncatedModel.FinitePointValueData.nativeGlobal q (ZMod q) n (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm)
    (A.truncatedShiftOver n m hm) (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
  P.paired.ambient P.paired.affine P.finiteOriginal hgood z hz

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_residue := Geometry.AbelianH1Model.TruncatedPairedPointParameters.BoundedResidues.source P z hgood hz
  (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceBelow P z hgood hz) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceCover P z hgood hz) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceGlobal P z hgood hz)

variable
  (he : IntegralComparison.Finite.SectionEvaluation.evaluation (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P) z = 1)
  (r : WittVector q (ZMod q))
  (hr : IntegralComparison.Truncated.Witt.quotient q (ZMod q) n r =
    Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidueScalar P (A.truncatedTraceDimension n+2) le_rfl)

include he hr in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_value : A.truncatedFinitePointValue n m hm =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) P.paired.original.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) •
          Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidue P (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)
            (Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_span P z hgood hz) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz))) := by
  have h := IntegralComparison.Truncated.PointFiniteValueFormula.comparison A n m hm
    P.paired.ambient P.paired.affine P.finiteOriginal hgood z hz he r hr
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation P z hgood hz).toRingHom
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.kernel P z hgood hz) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation_one P z hgood hz he)
  have hr' := Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_residue P z hgood hz
  have hw := congrArg (fun v =>
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) P.paired.original.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) • v))) hr'
  exact join_equalities h hw (by as_aux_lemma => rfl)

end Source

section Target
variable (V : (A.truncatedShiftModel n m hm).left.affineOpens)
  (hV : V.val ≤ Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P)
  (hcontains : ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ V.val)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetBelow := IntegralComparison.TruncatedModel.SmoothPointValueData.nativeBelow q (ZMod q) n (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n)
  P.paired.ambient P.paired.affine P.paired.transported (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
  (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains P V hV hcontains)
abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetCover := IntegralComparison.TruncatedModel.SmoothPointValueData.nativeCover q (ZMod q) n (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n)
  P.paired.ambient P.paired.affine P.paired.transported (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
  (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains P V hV hcontains)
abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetGlobal := IntegralComparison.TruncatedModel.SmoothPointValueData.nativeGlobal q (ZMod q) n (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n)
  P.paired.ambient P.paired.affine P.paired.transported (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
  (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains P V hV hcontains)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_residue := Geometry.AbelianH1Model.TruncatedPairedPointParameters.BoundedResidues.target P V hV hcontains
  (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetBelow P V hV hcontains) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetCover P V hV hcontains) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetGlobal P V hV hcontains)

variable (r : WittVector q (ZMod q))
  (hr : IntegralComparison.Truncated.Witt.quotient q (ZMod q) n r =
    Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidueScalar P (A.truncatedTraceDimension n+2) le_rfl)

include hr in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_value : A.truncatedOrdinaryPointValue n =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) P.paired.transported.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) •
          Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidue P V hV hcontains)) := by
  have h := IntegralComparison.Truncated.PointOrdinaryValueFormula.Ordinary.comparison A n
    P.paired.ambient P.paired.affine P.paired.transported
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains P V hV hcontains) r hr
  have hr' := Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_residue P V hV hcontains
  have hw := congrArg (fun v =>
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) P.paired.transported.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) • v))) hr'
  exact join_equalities h hw (by as_aux_lemma => rfl)
end Target

variable (z : Γ((A.truncatedShiftModel n m hm).left,Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P))
  (hgood : IntegralComparison.FiniteEtale.TraceBasis.Good (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P))
  (hz : Geometry.AbelianH1Model.TruncatedPairedPointParameters.IsComponent P z)
  (he : IntegralComparison.Finite.SectionEvaluation.evaluation (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P) z = 1)
  (hV : (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val ≤ Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P)
  (j : OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm))
  (hj : (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val ≤ OAI.AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens
    (TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) j)

include hgood hz he hV hj in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.equality : A.truncatedFinitePointValue n m hm = A.truncatedOrdinaryPointValue n := by
  obtain ⟨r,hs,ht⟩ := Geometry.AbelianH1Model.TruncatedPairedPointParameters.exists_commonResidueScalar P (A.truncatedTraceDimension n+2) le_rfl
  exact (Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_value P z hgood hz he r hs).trans
    ((Geometry.AbelianH1Model.TruncatedPairedPointParameters.weightedResidueComparison P (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) hV (Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)
      (Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_span P z hgood hz) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz) j hj r).trans
        (Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_value P (Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) hV (Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz) r ht).symm)

end TruncatedPairedPointParameters.PointValues

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedPointValues.AbelianModel
