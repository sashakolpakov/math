import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Form Symbol -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FormSymbol.FormSymbolAdditiveExt

noncomputable section

/-! Additive maps from native differential forms are determined by their symbols. -/

open OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u v

theorem ext (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
    (n : ℕ) {M : Type v} [AddCommGroup M] (f g : AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n →+ M)
    (h : ∀ b v, f (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B b v) = g (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B b v)) : f = g := by
  apply AddMonoidHom.ext
  intro ω
  obtain ⟨x, rfl⟩ := (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B n).mkQ_surjective ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v b => exact h b v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.FormSymbol.FormSymbolAdditiveExt
