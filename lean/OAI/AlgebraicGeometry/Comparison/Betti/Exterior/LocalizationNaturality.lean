import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Localization
import OAI.AlgebraicGeometry.Comparison.Betti.Exterior.Forms

/-! # Localization Naturality -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Exterior.LocalizationNaturality

noncomputable section

/-! The coefficient-linear localization map is the original pullback after scalar restriction. -/

open _root_.CategoryTheory

variable (A B : Type) [CommRing A] [CommRing B]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]

theorem oneFormsMap_toAlgHom (a : Ω[A⁄ℂ]) :
    Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap
      (CommAlgCat.ofHom (IsScalarTower.toAlgHom ℂ A B)) a =
      KaehlerDifferential.map ℂ ℂ A B a := by
  have ha : a ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_D, KaehlerDifferential.map_D]
      rfl
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul c x hx ih =>
      rw [Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.oneFormsMap_smul, map_smul, ih]
      exact algebraMap_smul B c (KaehlerDifferential.map ℂ ℂ A B x)

theorem coefficientExteriorMap_restrict (n : ℕ) :
    (Localization.coefficientExteriorMap ℂ A B n).restrictScalars ℂ =
      Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap
        (CommAlgCat.ofHom (IsScalarTower.toAlgHom ℂ A B)) n := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n (M := Ω[A⁄ℂ]))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  change Localization.coefficientExteriorMap ℂ A B n x = _
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      rw [Localization.coefficientExteriorMap_mk, Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_mk]
      congr 1
      funext i
      exact (oneFormsMap_toAlgHom A B (v i)).symm
  | zero => simp
  | add x y hx hy ihx ihy => simp only [map_add, ihx, ihy]
  | smul c x hx ih =>
      rw [map_smul, Crystalline.Cohomology.AlgebraicForms.AlgebraicDeRham.formsMap_smul, ih]
      exact (algebraMap_smul B c _).symm

theorem exteriorFormsEquiv_localization (n : ℕ) (a : Algebraic.Forms.Form A n) :
    Forms.exteriorFormsEquiv B n (Algebraic.Forms.pullback (IsScalarTower.toAlgHom ℂ A B) n a) =
      Localization.coefficientExteriorMap ℂ A B n (Forms.exteriorFormsEquiv A n a) := by
  rw [Forms.exteriorFormsEquiv_naturality]
  exact LinearMap.congr_fun (coefficientExteriorMap_restrict A B n).symm _

end

end OAI.AlgebraicGeometry.Comparison.Betti.Exterior.LocalizationNaturality
