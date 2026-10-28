import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductCoordinates

/-! # Refinement Product Reflect -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductReflect.Coordinates

noncomputable section

/-! Reflecting refinement quasi-isomorphisms through actual product
coordinates and isomorphisms of coefficient presheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v s t a b w
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {D : Type s} [Category.{t} D] [Quiver.IsThin D] [HasBinaryProducts D]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{w} A]
  (F : C ⥤ D) {ι κ : Type w} (U : ι → C) (V : κ → C)
  [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
  [∀ (n : ℕ) (z : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ z)) F]
  (r : FormalCoproduct.mk κ V ⟶ FormalCoproduct.mk ι U)

theorem reflect (P : Dᵒᵖ ⥤ A)
    [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map (F.obj ∘ U) (F.obj ∘ V)
      (RefinementProductCoordinates.mappedCover F U V r) P)] :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r (F.op ⋙ P)) := by
  apply (quasiIso_iff_comp_right _ (GeometricComparison.NonemptyCech.ProductBaseChange.NonemptyCechProductBaseChange.complexIso F V P).hom).mp
  rw [RefinementProductCoordinates.naturality]
  infer_instance

omit F [∀ (n : ℕ) (z : Fin (n + 1) → ι), PreservesLimit (Discrete.functor (U ∘ z)) F]
    [∀ (n : ℕ) (z : Fin (n + 1) → κ), PreservesLimit (Discrete.functor (V ∘ z)) F] in
theorem coefficients {P Q : Cᵒᵖ ⥤ A} (e : P ≅ Q)
    [QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r P)] :
    QuasiIso (GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.map U V r Q) := by
  apply (quasiIso_iff_comp_left ((NonemptyCechNerve.complexFunctor U).map e.hom) _).mp
  rw [GeometricComparison.NonemptyCech.Refinement.NonemptyCechRefinement.naturality]
  infer_instance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.RefinementProductReflect.Coordinates
