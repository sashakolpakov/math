import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedResidue
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedScalar
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.PointParameterKernel
import OAI.NumberTheory.PadicHodge.IntegralComparison.PrincipalResidue.ResidueRestriction

/-! # Paired Selected Parameters -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PairedSelectedParameters.Geometric.AbelianModel

noncomputable section

/-! The selected principal source open has the actual identity-section
ideal, with the original finite pullback parameters and section evaluation. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : GeometricComparison.Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra GeometricComparison.Geometry.AbelianH1Model.finiteSection_closed

local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.selectedFinite : IsFinite (A.truncatedShiftOver n m hm).left :=
  A.truncatedShiftMap_finite n m hm
local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.selectedEtale : AlgebraicGeometry.Etale (A.truncatedShiftOver n m hm).left :=
  A.truncatedShiftMap_etale n m hm
local instance _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.selectedSectionClosed :
    IsClosedImmersion (A.truncatedShiftIdentitySection n m hm ≫
      (A.truncatedShiftOver n m hm).left) := by
  change IsClosedImmersion (A.truncatedShiftIdentitySection n m hm ≫
    A.truncatedShiftMap n m hm)
  exact GeometricComparison.Geometry.AbelianH1Model.finiteSection_closed A n m hm

variable
  {U : (Projective.IntrinsicOverlap.Intrinsic.space (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

namespace TruncatedPairedPointParameters.SelectedParameters

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen : (A.truncatedModel n).scheme.left.Opens :=
  (A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen : (A.truncatedShiftModel n m hm).left.Opens :=
  (A.truncatedShiftMap n m hm) ⁻¹ᵁ GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_affine : IsAffineOpen (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) :=
  P.paired.affine.preimage (A.truncatedTraceMorphism n).left

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains :
    ⊤ ≤ (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm) ⁻¹ᵁ GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P :=
  (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).contains

private abbrev sourceScalar :
    Algebra Γ((A.truncatedModel n).scheme.left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P)
      Γ((A.truncatedShiftModel n m hm).left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P) :=
  AffineOpen.DeRhamTrace.sectionAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    (A.truncatedShiftOver n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P)

private abbrev targetScalar :
    Algebra Γ((A.truncatedModel n).scheme.left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) :=
  Finite.SectionEvaluation.quotientAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseParameters : Fin A.dimension → Γ((A.truncatedModel n).scheme.left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) :=
  ProjectivePoint.ParameterSource.parameters (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm)
    A.dimension P.paired.ambient P.paired.affine (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).toParameterData

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_span : Ideal.span (Set.range (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseParameters P)) =
    (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm).ker.ideal
      ⟨GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_affine P⟩ :=
  ProjectivePoint.ParameterSource.span (A.truncatedModel n).scheme
    (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm ≫ A.truncatedShiftMap n m hm)
    A.dimension P.paired.ambient P.paired.affine (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).toParameterData

variable (z : Γ((A.truncatedShiftModel n m hm).left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P))

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen : (A.truncatedShiftModel n m hm).left.affineOpens :=
  ⟨(A.truncatedShiftModel n m hm).left.basicOpen z,
    ((GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_affine P).preimage (A.truncatedShiftMap n m hm)).basicOpen z⟩

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below : (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val ≤
    ((A.truncatedShiftOver n m hm) ≫ A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient :=
  (A.truncatedShiftModel n m hm).left.basicOpen_le z

/-- The component condition uses the literal source and target section rings. -/
def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.IsComponent : Prop := by
  letI := sourceScalar P
  letI := targetScalar P
  exact ((1 : GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) ⊗ₜ[Γ((A.truncatedModel n).scheme.left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P)] z :
      (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) ⊗[Γ((A.truncatedModel n).scheme.left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P)]
        Γ((A.truncatedShiftModel n m hm).left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P)) =
    FiniteEtale.PointParameterKernel.component (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_affine P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.parameters_eq :
    GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z) =
      FiniteEtale.ParameterDifferentials.parameters (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
        (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
        (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseParameters P) z := rfl

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.principal_parameters :
    PrincipalResidue.ResidueRestriction.parameters
      ((A.truncatedShiftOver n m hm) ≫ A.truncatedTraceMorphism n).left
      P.paired.ambient (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).parameters =
        GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z) := by
  funext j
  exact ConcreteCategory.congr_hom
    (Scheme.Hom.comp_appLE (A.truncatedShiftMap n m hm) (A.truncatedTraceMorphism n).left
      P.paired.ambient (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)) ((GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).parameters j)

variable (hgood : FiniteEtale.TraceBasis.Good (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P)) (hz : GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.IsComponent P z)

include hgood hz in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains : ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val := by
  let := sourceScalar P
  let := targetScalar P
  exact FiniteEtale.PointParameterKernel.contains (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_affine P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P) hgood z hz

include hgood hz in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_span : Ideal.span (Set.range (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z))) =
    (A.truncatedShiftIdentitySection n m hm).ker.ideal (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) := by
  let := sourceScalar P
  let := targetScalar P
  rw [GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.parameters_eq P z]
  exact FiniteEtale.PointParameterKernel.ideal (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_affine P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P) hgood z hz
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseParameters P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_span P)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation :
    Intrinsic.SmoothClosedSections.ring (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val →ₐ[GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n]
        GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n :=
  Intrinsic.SectionEvaluation.evaluation (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftIdentitySection n m hm)
    (A.truncatedShiftIdentitySection_over n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation_restriction (a : Γ((A.truncatedShiftModel n m hm).left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P)) :
    GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation P z hgood hz
      ((A.truncatedShiftModel n m hm).left.presheaf.map (homOfLE (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)).op a) =
    Finite.SectionEvaluation.evaluation (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P) a :=
  Intrinsic.SectionEvaluation.restriction (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedShiftIdentitySection n m hm)
    (A.truncatedShiftIdentitySection_over n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz) a

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation_one
    (he : Finite.SectionEvaluation.evaluation (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm)
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.base_contains P) z = 1) :
    GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation P z hgood hz
      ((A.truncatedShiftModel n m hm).left.presheaf.map (homOfLE (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)).op z) = 1 :=
  (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation_restriction P z hgood hz z).trans he

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.kernel :
    Koszul.OrientedTopCohomology.ideal Γ((A.truncatedShiftModel n m hm).left,(GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val)
      (PrincipalResidue.ResidueRestriction.parameters
        ((A.truncatedShiftOver n m hm) ≫ A.truncatedTraceMorphism n).left
        P.paired.ambient (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).parameters) =
      RingHom.ker (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.evaluation P z hgood hz).toRingHom := by
  change Ideal.span (Set.range _) = _
  rw [GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.principal_parameters P z]
  exact (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_span P z hgood hz).trans
    (Intrinsic.SectionEvaluation.kernel (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
      (A.truncatedShiftModel n m hm) (A.truncatedShiftIdentitySection n m hm)
      (A.truncatedShiftIdentitySection_over n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).property).symm

end TruncatedPairedPointParameters.SelectedParameters

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PairedSelectedParameters.Geometric.AbelianModel
