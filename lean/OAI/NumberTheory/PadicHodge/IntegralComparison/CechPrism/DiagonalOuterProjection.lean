import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalComplex

/-! # Diagonal Outer Projection -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalOuterProjection

noncomputable section

/-! The native zeroth-row map has the literal outer Čech projection
prescribed by the local coefficient augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

theorem projection (j : ℕ) (b : Fin (j+1) → ι) :
    (DiagonalComplex.map U Q B γ h).f j ≫
      (Pi.π (fun b : Fin (j+1) → ι =>
        (NonemptyCechNerve.complexFunctor U).obj (B.obj (op (∏ᶜ (U ∘ b)))) ) b).f 0 =
      NonemptyCechDifferential.projection U Q j b ≫
        (DiagonalCone.coefficient U Q B γ h).app (op (∏ᶜ (U ∘ b))) := by
  apply Pi.hom_ext
  intro a
  exact (Category.assoc _ _ _).trans
    ((DiagonalComplex.map_projection U Q B γ h j a b).trans
      ((congrArg (fun m => NonemptyCechDifferential.projection U Q j b ≫ m)
        (DiagonalCone.coefficient_projection U Q B γ h
          (op (∏ᶜ (U ∘ b))) a).symm).trans (Category.assoc _ _ _).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalOuterProjection
