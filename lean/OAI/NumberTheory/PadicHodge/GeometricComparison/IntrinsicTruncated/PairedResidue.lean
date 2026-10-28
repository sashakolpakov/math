import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedParameterRestriction
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PointSupport
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.ParameterSource
import OAI.NumberTheory.PadicHodge.IntegralComparison.AffineOpen.ParameterRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidueNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.SupportedResidue

/-! # Paired Residue -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedResidue.AbelianModel

noncomputable section

/-! Restricting the original pointed frame identifies the two literal
supported residues for the paired parameters, with the same canonical
resolution and the actual identity-section supports. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} {A : Geometry.AbelianH1Model K q jq}
  {n m : ℕ} {hm : ¬q ∣ m}
attribute [local instance] MvPolynomial.gradedAlgebra
variable
  {U : (IntegralComparison.Projective.IntrinsicOverlap.Intrinsic.space (TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens}
  {hU : IsAffineOpen U}
  {D : IntegralComparison.ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedIdentitySection n) A.dimension U hU}
  (P : A.TruncatedPairedPointParameters n m hm U hU D)

namespace TruncatedPairedPointParameters

private abbrev residueResolution := injectiveResolution
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := q)
    (J := Ideal.span {(q : WittVector q (ZMod q))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers q (ZMod q))
    (IntegralComparison.Witt.Crystalline.wittStructureMap q (ZMod q) A.specialFiber.scheme) n)

variable (V : (A.truncatedShiftModel n m hm).left.affineOpens)
  (hV : V.val ≤ Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceNeighborhood P)
  (hVW : V.val ≤ (A.truncatedShiftMap n m hm) ⁻¹ᵁ
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient))

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters : Fin A.dimension → Γ((A.truncatedShiftModel n m hm).left,V.val) :=
  fun j => (A.truncatedShiftMap n m hm).appLE
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient) V.val hVW
    ((A.truncatedTraceMorphism n).left.app P.paired.ambient (P.paired.original.parameters j))

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters : Fin A.dimension →
    Γ((A.truncatedModel n).scheme.left,(Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).val) :=
  fun j => (A.truncatedModel n).scheme.left.presheaf.map
    (homOfLE (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV)).op
    ((A.truncatedTraceMorphism n).left.app P.paired.ambient (P.paired.transported.parameters j))

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.frame_parameters :
    IntegralComparison.TruncatedModel.SupportedReindexData.coefficients
      q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
      (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
      V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso P V hV) A.dimension
      (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW) = Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV := by
  funext j
  exact Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso_parameters P V hV hVW j

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_span : Ideal.span (Set.range (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV)) =
    (A.truncatedIdentitySection n).ker.ideal (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV) :=
  IntegralComparison.AffineOpen.ParameterRestriction.span (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedModel n).scheme
    ((A.truncatedTraceMorphism n).left ⁻¹ᵁ P.paired.ambient)
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).val (P.paired.affine.preimage (A.truncatedTraceMorphism n).left)
    (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV).property (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_below P V hV)
    (IntegralComparison.ProjectivePoint.ParameterSource.parameters (A.truncatedModel n).scheme
      (A.truncatedTraceMorphism n) (A.truncatedIdentitySection n) A.dimension
      P.paired.ambient P.paired.affine P.paired.transported.toParameterData)
    (A.truncatedIdentitySection n).ker
    (IntegralComparison.ProjectivePoint.ParameterSource.span (A.truncatedModel n).scheme
      (A.truncatedTraceMorphism n) (A.truncatedIdentitySection n) A.dimension
      P.paired.ambient P.paired.affine P.paired.transported.toParameterData)

variable (hsource : Ideal.span (Set.range (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW)) =
    (A.truncatedShiftIdentitySection n m hm).ker.ideal V)
  (hcontains : ⊤ ≤ (A.truncatedShiftIdentitySection n m hm) ⁻¹ᵁ V.val)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidue := IntegralComparison.TruncatedModel.SupportedResidue.residue
    q (ZMod q) n (A.truncatedShiftModel n m hm) A.specialFiber.scheme
    (A.truncatedShiftReduction n m hm) (A.truncatedShiftModel_square n m hm) V
    (residueResolution (A := A) (n := n)) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW)
    (IntegralComparison.TruncatedModel.SupportedSection.punctured q (ZMod q) n
      (A.truncatedShiftModel n m hm) A.specialFiber.scheme (A.truncatedShiftReduction n m hm)
      (A.truncatedShiftIdentitySection n m hm))
    (IntegralComparison.TruncatedModel.SupportedSection.below q (ZMod q) n (A.truncatedShiftModel n m hm)
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) V
      (A.truncatedShiftIdentitySection n m hm) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW) hsource)
    (IntegralComparison.TruncatedModel.SupportedSection.cover q (ZMod q) n (A.truncatedShiftModel n m hm)
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) V
      (A.truncatedShiftIdentitySection n m hm) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW) hsource)
    (IntegralComparison.TruncatedModel.SupportedRows.exactAt_succ q (ZMod q) n (A.truncatedShiftModel n m hm)
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) V
      (residueResolution (A := A) (n := n)) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW))
    (IntegralComparison.TruncatedModel.SupportedSection.global q (ZMod q) n (A.truncatedShiftModel n m hm)
      A.specialFiber.scheme (A.truncatedShiftReduction n m hm) V
      (A.truncatedShiftIdentitySection n m hm) hcontains)

def _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidue := IntegralComparison.TruncatedModel.SupportedResidue.residue
    q (ZMod q) n (A.truncatedModel n).scheme A.specialFiber.scheme
    (A.truncatedReduction n) (A.truncatedReductionSquare n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
    (residueResolution (A := A) (n := n)) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV)
    (IntegralComparison.TruncatedModel.SupportedSection.punctured q (ZMod q) n
      (A.truncatedModel n).scheme A.specialFiber.scheme (A.truncatedReduction n)
      (A.truncatedIdentitySection n))
    (IntegralComparison.TruncatedModel.SupportedSection.below q (ZMod q) n (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedReduction n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
      (A.truncatedIdentitySection n) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_span P V hV))
    (IntegralComparison.TruncatedModel.SupportedSection.cover q (ZMod q) n (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedReduction n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
      (A.truncatedIdentitySection n) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.target_span P V hV))
    (IntegralComparison.TruncatedModel.SupportedRows.exactAt_succ q (ZMod q) n (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedReduction n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
      (residueResolution (A := A) (n := n)) A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetParameters P V hV))
    (IntegralComparison.TruncatedModel.SupportedSection.global q (ZMod q) n (A.truncatedModel n).scheme
      A.specialFiber.scheme (A.truncatedReduction n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
      (A.truncatedIdentitySection n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget_contains P V hV hcontains))

variable (j : AlgebraicGeometry.Crystalline.Cohomology.Base.SmoothProperEtaleCover.BaseSmoothProperEtaleCover.Index (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm))
  (hj : V.val ≤ AlgebraicGeometry.Crystalline.Cohomology.Base.ProperOrdinaryFormCharts.BaseSmoothProperOrdinaryFormCharts.opens (TruncatedModel.NativeTruncatedBase.Ring q n)
    (A.truncatedShiftModel n m hm) j)

abbrev _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.rawResidueComparison :=
  IntegralComparison.TruncatedModel.SupportedResidueNaturality.section_comparison
    q (ZMod q) n (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme
    A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedReduction n)
    (A.truncatedShiftModel_square n m hm) (A.truncatedReductionSquare n)
    V (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedFrameIso P V hV)
    (residueResolution (A := A) (n := n)) j hj A.dimension (Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceParameters P V hVW)
    (A.truncatedShiftIdentitySection n m hm) hsource hcontains

include hj in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.residueComparison : Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidue P V hVW hsource hcontains = Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidue P V hV hcontains := by
  have h := Geometry.AbelianH1Model.TruncatedPairedPointParameters.rawResidueComparison P V hV hVW hsource hcontains j hj
  refine h.trans ?_
  apply IntegralComparison.TruncatedModel.SupportedResidue.Congruence.congr
    q (ZMod q) n (A.truncatedModel n).scheme A.specialFiber.scheme
    (A.truncatedReduction n) (A.truncatedReductionSquare n) (Geometry.AbelianH1Model.TruncatedPairedPointParameters.restrictedTarget P V hV)
    (residueResolution (A := A) (n := n)) A.dimension
  · exact Geometry.AbelianH1Model.TruncatedPairedPointParameters.frame_parameters P V hV hVW
  · exact A.truncatedIdentityPuncture_eq n m hm

include hj in
theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.TruncatedPairedPointParameters.weightedResidueComparison (r : WittVector q (ZMod q)) :
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) P.paired.original.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) •
          Geometry.AbelianH1Model.TruncatedPairedPointParameters.sourceResidue P V hVW hsource hcontains)) =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) P.paired.transported.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) •
          Geometry.AbelianH1Model.TruncatedPairedPointParameters.targetResidue P V hV hcontains)) := by
  rw [P.paired.same_codimension, Geometry.AbelianH1Model.TruncatedPairedPointParameters.residueComparison P V hV hVW hsource hcontains j hj]

end TruncatedPairedPointParameters

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.PairedResidue.AbelianModel
