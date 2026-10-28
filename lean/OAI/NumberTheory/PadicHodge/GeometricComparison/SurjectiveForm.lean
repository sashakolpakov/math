import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarMap

/-! # Surjective Form -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveForm.SurjectiveFormReduction

noncomputable section

/-! A surjection on coordinate rings induces a surjection on the actual differential-symbol modules in every degree. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]

theorem surjective (h : Function.Surjective (algebraMap A B)) (n : ℕ) :
    Function.Surjective (Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n) := by
  intro ω
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations S B n) ω
  induction x using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp only [map_zero]⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp only [map_add, ha, hb]⟩
  | single v b =>
    obtain ⟨a, rfl⟩ := h b
    choose w hw using fun i => h (v i)
    refine ⟨AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a w, ?_⟩
    change Forms.ScalarMap.FormsBaseChange.formExtensionMap R S A B n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a w) =
      AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap A B a) v
    rw [Forms.ScalarMap.FormsBaseChange.formExtensionMap_symbol]
    exact congrArg (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol S B (algebraMap A B a)) (funext hw)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.SurjectiveForm.SurjectiveFormReduction
