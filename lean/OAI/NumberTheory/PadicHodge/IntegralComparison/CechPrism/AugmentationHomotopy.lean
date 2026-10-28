import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.Homotopy
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.GlobalAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.DiagonalAugmentation

/-! # Augmentation Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.AugmentationHomotopy

noncomputable section

/-! The two actual Čech augmentations are homotopic through the
signed concatenation prism. No comparison or exactness hypothesis is
used: the inverse-meet maps supply the literal homotopy. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive Opposite

universe u v w t
variable {C : Type u} [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{t} A] [HasFiniteCoproducts A]
  {ι : Type t} [Finite ι] (U : ι → C)
  (Q : Cᵒᵖ ⥤ A) (B : Cᵒᵖ ⥤ Cᵒᵖ ⥤ A)
  (γ : (Functor.const Cᵒᵖ).obj Q ⟶ B)
  (h : ∀ I V : C, IsIso ((B.obj (op V)).map
    (homOfLE (inf_le_left : I ⊓ V ≤ I)).op))

local instance total : (IntrinsicComponents.Intrinsic.complex U B).HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts _

def homotopy : Homotopy (DiagonalAugmentation.map U Q B γ h)
    (GlobalAugmentation.map U Q B γ) :=
  CechPrism.Homotopy.homotopy U Q B γ h _ _ (by
    intro N p q hpq a b
    erw [sub_comp, DiagonalAugmentation.value_projection U Q B γ h N p q hpq,
      GlobalAugmentation.value_projection U Q B γ h N p q hpq])

theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (DiagonalAugmentation.map U Q B γ h) i =
      HomologicalComplex.homologyMap (GlobalAugmentation.map U Q B γ) i :=
  (homotopy U Q B γ h).homologyMap_eq i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechPrism.AugmentationHomotopy
