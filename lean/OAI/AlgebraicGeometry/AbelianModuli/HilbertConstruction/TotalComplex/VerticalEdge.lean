/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/TotalComplexUpNatVerticalEdge.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HorizontalEdge

/-! # Vertical Edge -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalEdge

/-!
# The vertical edge map into a first-quadrant total complex

Construct the vertical edge map by applying the horizontal construction to the
flipped bicomplex and transporting along mathlib's total-complex symmetry.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Preadditive

universe v u

open _root_.HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
variable [K.HasTotal (.up ℕ)]

/-- The vertical edge map from an augmented zeroth row to the total complex. -/
noncomputable def totalUpNatVerticalEdge
    (B : CochainComplex C ℕ) (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0) :
    B ⟶ K.total (.up ℕ) :=
  HorizontalEdge.totalUpNatHorizontalEdge K.flip B e he w ≫ (K.totalFlipIso (.up ℕ)).hom

@[simp]
theorem totalUpNatVerticalEdge_f
    (B : CochainComplex C ℕ) (e : ∀ p, B.X p ⟶ (K.X 0).X p)
    (he : ∀ p p', (ComplexShape.up ℕ).Rel p p' →
      e p ≫ (K.X 0).d p p' = B.d p p' ≫ e p')
    (w : ∀ p, e p ≫ (K.d 0 1).f p = 0) (p : ℕ) :
    (totalUpNatVerticalEdge K B e he w).f p =
      e p ≫ K.ιTotal (.up ℕ) 0 p p (by
        change 0 + p = p
        exact zero_add p) := by
  dsimp only [totalUpNatVerticalEdge, HomologicalComplex.comp_f]
  let j : (K.X 0).X p ⟶ (K.flip.total (.up ℕ)).X p :=
    K.flip.ιTotal (.up ℕ) p 0 p rfl
  let t : (K.flip.total (.up ℕ)).X p ⟶ (K.total (.up ℕ)).X p :=
    (K.totalFlipIso (.up ℕ)).hom.f p
  change (e p ≫ j) ≫ t = _
  rw [Category.assoc]
  have hj : j ≫ t = K.ιTotal (.up ℕ) 0 p p (by
      change 0 + p = p
      exact zero_add p) := by
    have hraw := K.ιTotal_totalFlipIso_f_hom (.up ℕ) 0 p p (by
      change p + 0 = p
      exact Nat.add_zero p)
    have hs : ComplexShape.σ (.up ℕ) (.up ℕ) (.up ℕ) 0 p = 1 := by
      simp
    rw [hs, one_smul] at hraw
    exact hraw
  rw [hj]

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.VerticalEdge
