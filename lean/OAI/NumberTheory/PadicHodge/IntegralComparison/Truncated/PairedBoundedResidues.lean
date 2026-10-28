import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PairedSelectedParameters
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.PrincipalSectionResidue

/-! # Paired Bounded Residues -/

namespace OAI.NumberTheory.PadicHodge

noncomputable section

/-! The two original principal fraction outputs are exactly the paired
supported residues, using the same resolution and identity-section supports. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : GeometricComparison.Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra GeometricComparison.Geometry.AbelianH1Model.finiteSection_closed
variable
  {U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

abbrev GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.resolution := injectiveResolution
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := q)
    (J := Ideal.span {(q : WittVector q (ZMod q))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) n)

section Source

variable (z : Γ((A.truncatedShiftModel n m hm).left,GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.fullOpen P))

abbrev GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceTuple := IntegralComparison.PrincipalResidue.ResidueRestriction.parameters
  ((A.truncatedShiftOver n m hm) ≫ A.truncatedTraceMorphism n).left
  P.paired.ambient (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)
  (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.finiteOriginal P).parameters

variable (hgood : IntegralComparison.FiniteEtale.TraceBasis.Good (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.baseOpen P))
  (hz : GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.IsComponent P z)
  (hO : IntegralComparison.TruncatedModel.PrincipalSectionResidue.Below q (ZMod q) n
    (A.truncatedShiftModel n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) A.dimension
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceTuple P z) (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedShiftIdentitySection n m hm).ker))
  (hcover : IntegralComparison.TruncatedModel.PrincipalSectionResidue.Cover q (ZMod q) n
    (A.truncatedShiftModel n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) A.dimension
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceTuple P z) (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedShiftIdentitySection n m hm).ker))
  (hglobal : IntegralComparison.TruncatedModel.PrincipalSectionResidue.Global q (ZMod q) n
    (A.truncatedShiftModel n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z)
    (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedShiftIdentitySection n m hm).ker))

theorem IntegralComparison.Truncated.PairedBoundedResidues.Geometric.AbelianModel.TruncatedPairedPointParameters.BoundedResidues.source :
    IntegralComparison.TruncatedModel.PrincipalFractionGlobal.boundedResidue q (ZMod q) n
      (A.truncatedShiftModel n m hm) A.specialFiber.scheme (A.truncatedShiftReduction n m hm)
      (A.truncatedShiftModel_square n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z)
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.resolution (A := A) (n := n)) A.dimension (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceTuple P z)
      (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedShiftIdentitySection n m hm).ker)
      hO hcover hglobal =
    GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidue P (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z)
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_span P z hgood hz) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz) := by
  have h := IntegralComparison.TruncatedModel.PrincipalSectionResidue.comparison q (ZMod q) n
    (A.truncatedShiftModel n m hm) A.specialFiber.scheme (A.truncatedShiftReduction n m hm)
    (A.truncatedShiftModel_square n m hm) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.resolution (A := A) (n := n)) A.dimension (A.truncatedShiftIdentitySection n m hm)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.affineOpen P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.below P z))
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.source_span P z hgood hz) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.contains P z hgood hz)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceTuple P z) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.principal_parameters P z) hO hcover hglobal
  exact h.trans (by as_aux_lemma => rfl)
alias GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.BoundedResidues.source := IntegralComparison.Truncated.PairedBoundedResidues.Geometric.AbelianModel.TruncatedPairedPointParameters.BoundedResidues.source

end Source

variable (V : (A.truncatedShiftModel n m hm).left.affineOpens)
  (hV : V.val ≤ GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P)

abbrev GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetTuple := IntegralComparison.PrincipalResidue.ResidueRestriction.parameters (A.truncatedTraceMorphism n).left
  P.paired.ambient (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).val (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV)
  P.paired.transported.parameters

theorem GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_parameters : GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetTuple P V hV = GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV := rfl

variable (hcontains : ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ V.val)
  (hO : IntegralComparison.TruncatedModel.PrincipalSectionResidue.Below q (ZMod q) n
    (A.truncatedModel n).scheme (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV) A.dimension
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetTuple P V hV) (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedIdentitySection n).ker))
  (hcover : IntegralComparison.TruncatedModel.PrincipalSectionResidue.Cover q (ZMod q) n
    (A.truncatedModel n).scheme (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV) A.dimension
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetTuple P V hV) (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedIdentitySection n).ker))
  (hglobal : IntegralComparison.TruncatedModel.PrincipalSectionResidue.Global q (ZMod q) n
    (A.truncatedModel n).scheme (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
    (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedIdentitySection n).ker))

theorem IntegralComparison.Truncated.PairedBoundedResidues.Geometric.AbelianModel.TruncatedPairedPointParameters.BoundedResidues.target :
    IntegralComparison.TruncatedModel.PrincipalFractionGlobal.boundedResidue q (ZMod q) n
      (A.truncatedModel n).scheme A.specialFiber.scheme (A.truncatedReduction n)
      (A.truncatedReductionSquare n) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
      (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.resolution (A := A) (n := n)) A.dimension (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetTuple P V hV)
      (IntegralComparison.SectionIdealPuncturedCover.outside (A.truncatedIdentitySection n).ker)
      hO hcover hglobal = GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidue P V hV hcontains := by
  have h := IntegralComparison.TruncatedModel.PrincipalSectionResidue.comparison q (ZMod q) n
    (A.truncatedModel n).scheme A.specialFiber.scheme (A.truncatedReduction n)
    (A.truncatedReductionSquare n) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.resolution (A := A) (n := n)) A.dimension (A.truncatedIdentitySection n)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_span P V hV) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains P V hV hcontains)
    (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetTuple P V hV) (GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_parameters P V hV) hO hcover hglobal
  exact h.trans (by as_aux_lemma => rfl)
alias GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.BoundedResidues.target := IntegralComparison.Truncated.PairedBoundedResidues.Geometric.AbelianModel.TruncatedPairedPointParameters.BoundedResidues.target

end

end OAI.NumberTheory.PadicHodge
