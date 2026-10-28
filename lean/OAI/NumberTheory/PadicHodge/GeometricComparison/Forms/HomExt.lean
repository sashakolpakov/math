import OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamGlobalId

/-! # Hom Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.HomExt.FormsHomExt

noncomputable section

/-! Maps out of the actual form module are determined by differential symbols. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation

universe u

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B] (n : ℕ)

theorem hom_ext (N : ModuleCat.{u} R) {f g : ModuleCat.of R (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R B n) ⟶ N}
    (h : ∀ b v, f (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B b v) = g (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R B b v)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro ω
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R B n) ω
  induction x using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | single v b => exact h b v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.HomExt.FormsHomExt
