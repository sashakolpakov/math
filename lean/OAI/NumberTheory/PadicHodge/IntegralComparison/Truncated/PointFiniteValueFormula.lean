import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointValueTraceCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.TruncatedModel.FinitePointValue
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicTruncated.ClosedPoint

/-! # Point Finite Value Formula -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointFiniteValueFormula

noncomputable section

/-! The original finite point value expressed on its selected principal
source neighborhood, before identifying the paired local residue. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex
open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic
open OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : GeometricComparison.Geometry.AbelianH1Model K q jq) (n m : ℕ) (hm : ¬q ∣ m)
attribute [local instance] MvPolynomial.gradedAlgebra IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra
  IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
local instance finiteMap : IsFinite (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_finite n m hm
local instance etaleMap : Etale (A.truncatedShiftOver n m hm).left := A.truncatedShiftMap_etale n m hm
variable (U : (Projective.IntrinsicOverlap.Intrinsic.space (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedTraceDimension n+1)).Opens)
  (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data (A.truncatedModel n).scheme (A.truncatedTraceMorphism n)
    (A.truncatedShiftIdentitySection n m hm ≫ (A.truncatedShiftOver n m hm).left)
    A.dimension U hU)
  (hgood : FiniteEtale.TraceBasis.Good (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm) ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U))
  (z : IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U)
  (hz :
    letI : Algebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U)
    letI : Algebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) ((A.truncatedShiftOver n m hm).left ⁻¹ᵁ ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm) (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm) ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) D.contains
    letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) := hgood.2.2
    letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) := (A.truncatedShiftOver n m hm).left.finite_app _ hgood.1
    letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) :=
      AffineOpen.DeRhamTrace.sectionEtale (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) (A.truncatedModel n).scheme (A.truncatedShiftOver n m hm) ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) hgood.1
    (1 ⊗ₜ[IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U] z : (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) ⊗[IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U] IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) =
      FiniteEtale.FiberSectionTrace.component (IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n)
        (IntegralComparison.Finite.SectionEvaluation.evaluation (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm) (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm) ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) D.contains))
  (he :
    letI : Algebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (IntegralComparison.Finite.FlatCoefficientSections.quotientRing (A.truncatedTraceMorphism n).left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U)
    letI : Algebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing (A.truncatedShiftOver n m hm).left (A.truncatedTraceMorphism n).left U) :=
      AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedShiftModel n m hm) ((A.truncatedShiftOver n m hm).left ⁻¹ᵁ ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U))
    letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm) (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm) ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) D.contains
    IntegralComparison.Finite.SectionEvaluation.evaluation (GeometricComparison.IntrinsicTruncated.TruncatedModel.NativeTruncatedBase.Ring q n) (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm) (A.truncatedShiftIdentitySection n m hm) (A.truncatedShiftIdentitySection_over n m hm) ((A.truncatedTraceMorphism n).left ⁻¹ᵁ U) D.contains z = 1)

abbrev selectedOpen := TruncatedModel.FinitePointValueData.selectedOpen q (ZMod q) n
  (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
  (A.truncatedTraceMorphism n) U hgood z

abbrev parameters := TruncatedModel.FinitePointValueData.parameters q (ZMod q) n
  (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
  (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm) U hU D hgood z

abbrev residue := TruncatedModel.FinitePointValueData.residue q (ZMod q) n
  (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
  (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
  (A.truncatedShiftIdentitySection_over n m hm) U hU D hgood z hz
  A.specialFiber.scheme (A.truncatedShiftReduction n m hm) (A.truncatedShiftModel_square n m hm)
  (A.truncatedPointValueResolution n)

variable (r : WittVector q (ZMod q))
  (hr : Witt.quotient q (ZMod q) n r =
    TruncatedModel.FinitePointValueData.rawValue q (ZMod q) n
      (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
      (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
      (A.truncatedShiftIdentitySection_over n m hm) (A.truncatedTraceDimension n+2) le_rfl U hU D)
  {κ : Type} [CommRing κ]
  (η : Γ((A.truncatedShiftModel n m hm).left,(selectedOpen A n m hm U hgood z).val) →+* κ)
  (hk : Koszul.OrientedTopCohomology.ideal
      Γ((A.truncatedShiftModel n m hm).left,(selectedOpen A n m hm U hgood z).val)
      (parameters A n m hm U hU D hgood z) = RingHom.ker η)
  (hzlocal : η ((A.truncatedShiftModel n m hm).left.presheaf.map
      (homOfLE (TruncatedModel.FinitePointValueData.selectedBelow q (ZMod q) n
        (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
        (A.truncatedTraceMorphism n) U hgood z)).op z) = 1)

attribute [local irreducible] HomologicalComplex.homology Intrinsic.EtaleProperTraceBase.IntrinsicFinite.serreIso

include he hr hk hzlocal in
theorem comparison : A.truncatedFinitePointValue n m hm =
    ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) D.codimension A.dimension •
      (ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) A.dimension A.dimension •
        ((⟨r⟩ : Crystalline.ExactRestriction.Coeff (B := WittVector q (ZMod q))) •
          residue A n m hm U hU D hgood z hz)) := by
  have h := TruncatedModel.FinitePointValue.global_fraction q (ZMod q) n
    (A.truncatedModel n).scheme (A.truncatedShiftModel n m hm) (A.truncatedShiftOver n m hm)
    (A.truncatedTraceMorphism n) (A.truncatedShiftIdentitySection n m hm)
    (A.truncatedShiftIdentitySection_over n m hm) (A.truncatedTraceDimension n+2) le_rfl
    U hU D hgood z hz he A.specialFiber.scheme (A.truncatedShiftReduction n m hm)
    (A.truncatedShiftModel_square n m hm) (A.truncatedPointValueResolution n) r hr η hk hzlocal
  refine (PointValueTraceCoordinates.finite A n m hm).symm.trans ?_
  dsimp only [PointValueTraceCoordinates.finiteValue,
    PointValueTraceCoordinates.finiteGlobalMap, residue]
  dsimp only [TruncatedModel.FinitePointValueData.cover,
    TruncatedModel.FinitePointValueData.coverFull] at h
  exact h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.PointFiniteValueFormula
