import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionPresheaf
import OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveForm

/-! # Reduction Sections -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionSections.IntrinsicIntegralReductionSections

noncomputable section

/-! Surjective geometric section maps give surjective native reduction maps on form presheaf sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.GeometricComparison.OpenSectionBase.OpenSectionScalarAlgebras

variable (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
  (X : Over (Spec (CommRingCat.of R))) (Y : Over (Spec (CommRingCat.of S)))
  (f : Y.left ⟶ X.left)
  (h : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))

theorem surjective (U : X.left.Opens) (hU : Function.Surjective (f.app U)) (n : ℕ) :
    Function.Surjective (ReductionPresheaf.IntrinsicIntegralReductionPresheaf.component R S X Y f h U n) := by
  let : Algebra R Γ(X.left, U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra R X U
  let : Algebra S Γ(Y.left, f ⁻¹ᵁ U) := AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.sectionAlgebra S Y (f ⁻¹ᵁ U)
  let : Algebra R Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.baseAlgebra R S X Y f U
  let : Algebra Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceAlgebra R S X Y f U
  let : IsScalarTower R S Γ(Y.left, f ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let : IsScalarTower R Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) := OpenSectionBase.OpenSectionScalarAlgebras.sourceTower R S X Y f U h
  have hh := SurjectiveForm.SurjectiveFormReduction.surjective R S Γ(X.left, U) Γ(Y.left, f ⁻¹ᵁ U) hU n
  exact hh

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicIntegral.ReductionSections.IntrinsicIntegralReductionSections
