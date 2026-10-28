import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalRowNormalization

/-! # Diagonal Total Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalTotalNormalization

noncomputable section

/-! After canonical regrouping, the original total diagonal edge is
exactly the Čech total of the local diagonal augmentation. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ CochainComplex A ℕ)
  (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ CochainComplex A ℕ)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))
attribute [local instance] TripleTotal.Rotation.total TripleTotal.Rotation.complexTotal

local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.RowCoordinates.rowFunctor (A := A)
local notation "P" => B ⋙ OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U
local notation "K" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U) Q
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic.complex U B
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalComplex.map U Q B γ h
local notation "w₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalAugmentation.cocycle U Q B γ h

theorem map_eq : TripleTotal.VerticalEdge.map S K a w₀ ≫
    DoubleCechRegrouping.map U P =
      (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map
        (LocalAugmentation.map U Q B γ h) := by
  change TripleTotal.VerticalEdge.map S K a w₀ ≫
    (TripleTotal.RowCoordinates.regroup S ≫ (DoubleCechRegrouping.totalIso U P).hom) = _
  erw [← Category.assoc, TripleTotal.VerticalEdge.regroup]
  change (F).map (TripleTotal.VerticalEdge.rowMap S K a w₀) ≫
    (F).map (DiagonalRowNormalization.coefficientIso U B).hom = _
  exact ((F).map_comp (TripleTotal.VerticalEdge.rowMap S K a w₀)
    (DiagonalRowNormalization.coefficientIso U B).hom).symm.trans
      (congrArg (F).map (DiagonalRowNormalization.map_eq U Q B γ h))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalTotalNormalization
