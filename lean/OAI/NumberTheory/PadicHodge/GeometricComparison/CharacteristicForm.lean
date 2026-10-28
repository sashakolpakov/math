import OAI.AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD

/-! # Characteristic Form -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicForm.CharacteristicFormPullback

noncomputable section

/-! A map killing exact one-forms kills pullback on every positive-degree differential-symbol module, in arbitrary characteristic. -/

open _root_.CategoryTheory

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable {R : Type u} [CommRing R] {A B : CommAlgCat.{u} R} (f : A ⟶ B)

theorem map_zero (h : ∀ a : A, KaehlerDifferential.D R B (f a) = 0)
    (n : ℕ) (hn : 0 < n) (ω : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) : AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n ω = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | single v a =>
    change AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap f n (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = 0
    rw [AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId.DeRhamGlobal.formMap_symbol, AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol_smul_one, ← AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols_D]
    rw [(AlgebraicGeometry.Crystalline.Cohomology.FormsEquivalenceD.FormsEquivalence.liftedSymbols R B n).map_coord_zero ⟨0, hn⟩ (h (v ⟨0, hn⟩)), smul_zero]

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CharacteristicForm.CharacteristicFormPullback
