import OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.HomExt
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Scalar Hom Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarHomExt.FormsHomExt

noncomputable section

/-! Maps out of scalar-extended native forms are determined by pure tensors of differential symbols. -/

open _root_.CategoryTheory OAI.AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation
open scoped TensorProduct

universe u

variable (R S A : Type u) [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] (n : ℕ)

theorem scalar_hom_ext (N : ModuleCat.{u} S)
    {f g : ModuleCat.of S (S ⊗[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.Form R A n) ⟶ N}
    (h : ∀ s a v, f (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v) = g (s ⊗ₜ[R] AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.symbol R A a v)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s ω =>
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (AlgebraicGeometry.Crystalline.Cohomology.DeRhamPresentationTo.DeRhamPresentation.relations R A n) ω
    induction x using Finsupp.induction_linear with
    | zero => simp only [map_zero, TensorProduct.tmul_zero]
    | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
    | single v a => exact h s a v

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Forms.ScalarHomExt.FormsHomExt
