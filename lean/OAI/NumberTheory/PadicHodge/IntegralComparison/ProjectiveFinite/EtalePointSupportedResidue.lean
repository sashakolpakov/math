import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointResidue
import OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectivePoint.PointParameterData
import OAI.NumberTheory.PadicHodge.IntegralComparison.FiniteEtale.FiberSectionSupport

/-! # Etale Point Supported Residue -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointSupportedResidue

noncomputable section

/-! The genuine projective point chart gives the actual finite residue
with its numerator supported in any prescribed neighborhood of the
source section, without changing the coefficient ring or scalar residue. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MvPolynomial Opposite
open OAI.NumberTheory.PadicHodge.IntegralComparison.Projective.IntrinsicOverlap.Intrinsic OAI.NumberTheory.PadicHodge.IntegralComparison.Finite.FlatCoefficientSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [Module.Injective R R]
  [IsArtinianRing R] [IsLocalRing R] {n g : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra IntegralComparison.Finite.FlatCoefficientSections.quotientAlgebra
  IntegralComparison.Finite.FlatCoefficientSections.coefficientAlgebra IntegralComparison.Finite.FlatCoefficientSections.ambientAlgebra
variable (X Y : Over (Spec (CommRingCat.of R))) [Nonempty X.left] (f : Y ⟶ X)
  [IsFinite f.left] [Etale f.left]
  (i : X ⟶ Projective.IntrinsicOverlap.Intrinsic.model R (n+1)) [IsClosedImmersion i.left]
  [Smooth X.hom] [IsProper X.hom] [GeometricallyConnected X.hom]
  [Smooth Y.hom] [IsProper Y.hom] [GeometricallyConnected Y.hom]
  [SmoothOfRelativeDimension g X.hom]
  (s₀ : Spec (CommRingCat.of R) ⟶ Y.left) (hbase : s₀ ≫ Y.hom = 𝟙 _)
  (B : ℕ) (hB : n+2 ≤ B)
  (U : (Projective.IntrinsicOverlap.Intrinsic.space R (n+1)).Opens) (hU : IsAffineOpen U)
  (D : ProjectivePoint.PointParameterData.Chart.Data X i (s₀ ≫ f.left) g U hU)
  (hgood : FiniteEtale.TraceBasis.Good R Y X f (i.left ⁻¹ᵁ U))
  (V : Y.left.Opens) (hV : ⊤ ≤ s₀ ⁻¹ᵁ V)

abbrev exists_residue := by
  letI := D.finiteVariables
  letI := D.coordinates
  letI := D.coordinateTower
  letI := D.coordinateEtale
  letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X (i.left ⁻¹ᵁ U)
  letI : Algebra R (IntegralComparison.Finite.FlatCoefficientSections.coefficientRing f.left i.left U) :=
    AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))
  letI := IntegralComparison.Finite.SectionEvaluation.quotientAlgebra R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
  letI : Algebra (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U)
      (Intrinsic.SmoothClosedSections.ring R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))) :=
    AffineOpen.DeRhamTrace.sectionAlgebra R Y X f (i.left ⁻¹ᵁ U)
  letI : Module.Free (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U)
      (Intrinsic.SmoothClosedSections.ring R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))) := hgood.2.2
  letI : Module.Finite (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U)
      (Intrinsic.SmoothClosedSections.ring R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))) :=
    f.left.finite_app _ hgood.1
  letI : Algebra.Etale (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U)
      (Intrinsic.SmoothClosedSections.ring R Y (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U))) :=
    AffineOpen.DeRhamTrace.sectionEtale R Y X f (i.left ⁻¹ᵁ U) hgood.1
  let ε := IntegralComparison.Finite.SectionEvaluation.evaluation R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains
  have hε : ε.toRingHom = (Intrinsic.SectionEvaluation.evaluation R Y s₀ hbase
      (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) D.contains).toRingHom := rfl
  have hsupport := FiniteEtale.FiberSectionSupport.exists_supported
    R Y s₀ hbase (f.left ⁻¹ᵁ (i.left ⁻¹ᵁ U)) (hgood.1.preimage f.left) D.contains
    (IntegralComparison.Finite.FlatCoefficientSections.quotientRing i.left U) ε hε V hV
    (IntegralComparison.Finite.SectionEvaluation.surjective R X Y f s₀ hbase (i.left ⁻¹ᵁ U) D.contains)
  exact Exists.imp (fun z hzall => by
    rcases hzall with ⟨hz, hzε, hzV, hzcontains⟩
    have he := EtalePointResidue.eq_residue D.dimension X Y f i s₀ hbase B hB
      U hU D.contains hgood D.coordinate D.below_coordinate D.equations D.generates D.regular
      D.conormalBasis D.conormalBasis_apply D.quotientBasis D.parameters D.quotientBasis_apply
      D.point_generates D.point_regular D.ambientBasis D.ambientBasis_apply D.coordinateIndex z hz
    exact And.intro hz (And.intro hzε (And.intro hzV (And.intro hzcontains he)))) hsupport

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ProjectiveFinite.EtalePointSupportedResidue
