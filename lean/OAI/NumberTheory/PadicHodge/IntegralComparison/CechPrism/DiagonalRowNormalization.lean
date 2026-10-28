import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.LocalAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalOuterProjection
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.DoubleCechRegrouping
import OAI.NumberTheory.PadicHodge.IntegralComparison.TripleTotal.VerticalEdge

/-! # Diagonal Row Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalRowNormalization

noncomputable section

/-! The regrouped diagonal edge is the original Čech map of the
local diagonal augmentations, in the actual row-total coordinates. -/

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
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U
local notation "K" => Functor.obj (OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.complexFunctor U) Q
local notation "S" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.IntrinsicComponents.Intrinsic.complex U B
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalComplex.map U Q B γ h
local notation "w₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalAugmentation.cocycle U Q B γ h

omit [HasCoproducts.{0} A] [Finite ι] in
theorem zeroMap (V : Cᵒᵖ) : GeometricComparison.CechCone.Total.CechConeTotal.zeroMap U (B.obj V) (Q.obj V)
    (LocalAugmentation.cone Q B γ h V) =
      (DiagonalCone.coefficient U Q B γ h).app V := rfl

def coefficientIso := GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.complexIso F N
  (fun _ => inferInstanceAs (Finite (Fin _ → ι))) P

def map := TripleTotal.VerticalEdge.rowMap S K a w₀ ≫ (coefficientIso U B).hom

theorem map_eq : DiagonalRowNormalization.map U Q B γ h = (NonemptyCechNerve.complexFunctor U).map
    (LocalAugmentation.map U Q B γ h) := by
  apply HomologicalComplex.Hom.ext
  funext j
  apply Pi.hom_ext
  intro (b : Fin (j+1) → ι)
  change ((TripleTotal.VerticalEdge.rowMap S K a w₀).f j ≫
    (coefficientIso U B).hom.f j) ≫ Pi.π
      (fun b : Fin (j+1) → ι => (F).obj ((P).obj (op (∏ᶜ (U ∘ b))))) b = _
  dsimp only [coefficientIso]
  erw [Category.assoc, GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.hom_f, piComparison_comp_π]
  change (TripleTotal.VerticalEdge.rowMap S K a w₀).f j ≫
    (F).map (Pi.π (fun b : Fin (j+1) → ι => (P).obj (op (∏ᶜ (U ∘ b)))) b) =
      Limits.Pi.map (fun b : Fin (j+1) → ι =>
        (LocalAugmentation.map U Q B γ h).app (op (∏ᶜ (U ∘ b)))) ≫ Pi.π _ b
  erw [Pi.map_π]
  apply HomologicalComplex.Hom.ext
  funext r
  change (((a).f j).f r ≫
      (HomologicalComplex₂.flip ((HomologicalComplex₂.flip S).X j)).ιTotal (.up ℕ) r 0 r rfl) ≫
    (HomologicalComplex₂.total.map
      ((HomologicalComplex₂.flipFunctor A (.up ℕ) (.up ℕ)).map
        (Pi.π (fun b : Fin (j+1) → ι => (P).obj (op (∏ᶜ (U ∘ b)))) b)) (.up ℕ)).f r = _
  erw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc]
  have hp := congrArg
    (fun m : (K).X j ⟶ ((P).obj (op (∏ᶜ (U ∘ b)))).X 0 => m.f r)
    (DiagonalOuterProjection.projection U Q B γ h j b)
  change ((a).f j).f r ≫
    ((Pi.π (fun b : Fin (j+1) → ι => (P).obj (op (∏ᶜ (U ∘ b)))) b).f 0).f r =
      (NonemptyCechDifferential.projection U Q j b).f r ≫
        ((DiagonalCone.coefficient U Q B γ h).app (op (∏ᶜ (U ∘ b)))).f r at hp
  change (((a).f j).f r ≫
    ((Pi.π (fun b : Fin (j+1) → ι => (P).obj (op (∏ᶜ (U ∘ b)))) b).f 0).f r) ≫ _ = _
  erw [hp, Category.assoc]
  change _ = (NonemptyCechDifferential.projection U Q j b).f r ≫
    ((GeometricComparison.CechCone.Total.CechConeTotal.zeroMap U (B.obj (op (∏ᶜ (U ∘ b)))) (Q.obj (op (∏ᶜ (U ∘ b))))
      (LocalAugmentation.cone Q B γ h (op (∏ᶜ (U ∘ b))))).f r ≫ _)
  rw [zeroMap]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalRowNormalization
