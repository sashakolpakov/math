import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Opposites

/-! # Block -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Block.Construction.Blocks

/-!
# CartierDuality: restriction of duality to adjoint direct factors

This is a categorical helper for the polarization step. Its input is an
ambient duality isomorphism and actual splittings of the two projectors;
the restricted duality is constructed, not included in the input data.
-/

open _root_.CategoryTheory Opposite

universe u v

variable {C : Type u} [Category.{v} C]
variable (D : Cᵒᵖ ⥤ C)
variable {X Y X₀ Y₀ : C}

/-- An ambient duality restricts to a duality of direct factors when the
two projection idempotents are adjoint under the ambient pairing. -/
def adjointFactorsIso
    (e : Y ≅ D.obj (op X))
    (ix : X₀ ⟶ X) (rx : X ⟶ X₀) (hx : ix ≫ rx = 𝟙 X₀)
    (iy : Y₀ ⟶ Y) (ry : Y ⟶ Y₀) (hy : iy ≫ ry = 𝟙 Y₀)
    (hadj : (ry ≫ iy) ≫ e.hom = e.hom ≫ D.map (rx ≫ ix).op) :
    Y₀ ≅ D.obj (op X₀) where
  hom := iy ≫ e.hom ≫ D.map ix.op
  inv := D.map rx.op ≫ e.inv ≫ ry
  hom_inv_id := by
    calc
      (iy ≫ e.hom ≫ D.map ix.op) ≫ (D.map rx.op ≫ e.inv ≫ ry) =
          iy ≫ (e.hom ≫ D.map (rx ≫ ix).op) ≫ e.inv ≫ ry := by
            simp only [op_comp, D.map_comp, Category.assoc]
      _ = iy ≫ (ry ≫ iy) ≫ ry := by rw [← hadj]; simp
      _ = 𝟙 Y₀ := by simp only [← Category.assoc, hy, Category.id_comp]
  inv_hom_id := by
    calc
      (D.map rx.op ≫ e.inv ≫ ry) ≫ (iy ≫ e.hom ≫ D.map ix.op) =
          D.map rx.op ≫ e.inv ≫ ((ry ≫ iy) ≫ e.hom) ≫ D.map ix.op := by
            simp only [Category.assoc]
      _ = D.map rx.op ≫ D.map (rx ≫ ix).op ≫ D.map ix.op := by
        rw [hadj]
        simp
      _ = 𝟙 (D.obj (op X₀)) := by
        rw [← D.map_comp, ← D.map_comp]
        simp only [← op_comp, ← Category.assoc, hx, Category.id_comp, op_id, D.map_id]

@[simp]
theorem adjointFactorsIso_hom
    (e : Y ≅ D.obj (op X))
    (ix : X₀ ⟶ X) (rx : X ⟶ X₀) (hx : ix ≫ rx = 𝟙 X₀)
    (iy : Y₀ ⟶ Y) (ry : Y ⟶ Y₀) (hy : iy ≫ ry = 𝟙 Y₀)
    (hadj : (ry ≫ iy) ≫ e.hom = e.hom ≫ D.map (rx ≫ ix).op) :
    (adjointFactorsIso D e ix rx hx iy ry hy hadj).hom =
      iy ≫ e.hom ≫ D.map ix.op := rfl

end OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.Block.Construction.Blocks
