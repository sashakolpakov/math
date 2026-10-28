import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModulePresheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.LocalizationNaturality

/-! # Module Localization -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleLocalization

noncomputable section

/-! Localization for the actual restriction maps of the exterior-form module presheaf. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham

variable {C : Type*} [Category C] (F : Cᵒᵖ ⥤ CommAlgCat.{0} ℂ)
  {U V : Cᵒᵖ} (f : U ⟶ V)

def formModuleMapCoefficient (n : ℕ) :
    letI := (F.map f).hom.toRingHom.toAlgebra
    Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (F.obj U) n →ₗ[F.obj U] Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.Forms (F.obj V) n :=
  (ModulePresheaf.formModuleMap F f n).hom

theorem formModuleMapCoefficient_eq (n : ℕ) :
    letI := (F.map f).hom.toRingHom.toAlgebra
    formModuleMapCoefficient F f n = Localization.coefficientExteriorMap ℂ (F.obj U) (F.obj V) n := by
  let := (F.map f).hom.toRingHom.toAlgebra
  have he : IsScalarTower.toAlgHom ℂ (F.obj U) (F.obj V) = (F.map f).hom := by
    ext a
    rfl
  apply LinearMap.ext
  intro ω
  have h := LinearMap.congr_fun
    (LocalizationNaturality.coefficientExteriorMap_restrict (F.obj U) (F.obj V) n).symm ω
  rw [he] at h
  exact h

theorem formModuleMapCoefficient_isLocalizedModule (S : Submonoid (F.obj U))
    (hS : letI := (F.map f).hom.toRingHom.toAlgebra; IsLocalization S (F.obj V))
    [Module.Free (F.obj U) Ω[F.obj U⁄ℂ]] (n : ℕ) :
    letI := (F.map f).hom.toRingHom.toAlgebra
    IsLocalizedModule S (formModuleMapCoefficient F f n) := by
  let := (F.map f).hom.toRingHom.toAlgebra
  have : IsLocalization S (F.obj V) := hS
  rw [formModuleMapCoefficient_eq]
  exact Localization.coefficientExteriorMap_isLocalizedModule ℂ (F.obj U) (F.obj V) S n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.ModuleLocalization
