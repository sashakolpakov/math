import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.AlgebraicGeometry.Limits

/-! # Over Product Tensor Comparison -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverProductTensorComparison

noncomputable section

/-! Explicit comparison of the ordinary product notation in Presentations with
the chosen cartesian tensor products used by the HilbertConstruction Segre construction. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u
variable {S : Scheme.{u}} (X Y : Over S)

def overProductTensorIso : (X ⨯ Y) ≅ (X ⊗ Y) where
  hom := CartesianMonoidalCategory.lift prod.fst prod.snd
  inv := prod.lift (CartesianMonoidalCategory.fst X Y) (CartesianMonoidalCategory.snd X Y)
  hom_inv_id := by
    apply prod.hom_ext <;> simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext <;> simp

theorem overProductTensorIso_hom_fst :
    (overProductTensorIso X Y).hom ≫ CartesianMonoidalCategory.fst X Y = prod.fst :=
  CartesianMonoidalCategory.lift_fst _ _

theorem overProductTensorIso_hom_snd :
    (overProductTensorIso X Y).hom ≫ CartesianMonoidalCategory.snd X Y = prod.snd :=
  CartesianMonoidalCategory.lift_snd _ _

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.OverProductTensorComparison
