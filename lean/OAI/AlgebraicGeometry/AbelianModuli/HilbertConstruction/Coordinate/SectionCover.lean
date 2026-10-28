import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Line.Bundles
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Section Cover -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionCover

noncomputable section

/-! Actual affine coordinate opens and their regular coordinate ratios, in the form needed to extend sections of quasicoherent modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

structure CoordinateSectionCover (X : Scheme.{u}) (ι : Type v) where
  opens : ι → X.Opens
  affine : ∀ i, IsAffineOpen (opens i)
  affine_overlap : ∀ i k, IsAffineOpen (opens i ⊓ opens k)
  covers : ∀ x : X, ∃ i, x ∈ opens i
  ratio : ∀ i, ι → Γ(X, opens i)
  ratio_self : ∀ i, ratio i i = 1
  basicOpen_ratio : ∀ i j, X.basicOpen (ratio i j) = opens i ⊓ opens j
  ratio_transition : ∀ i k j,
    X.presheaf.map (homOfLE (show opens i ⊓ opens k ≤ opens i from inf_le_left)).op (ratio i j) =
      X.presheaf.map (homOfLE (show opens i ⊓ opens k ≤ opens i from inf_le_left)).op (ratio i k) *
      X.presheaf.map (homOfLE (show opens i ⊓ opens k ≤ opens k from inf_le_right)).op (ratio k j)

namespace CoordinateSectionCover

variable {X : Scheme.{u}} {ι : Type v} (D : CoordinateSectionCover X ι)

abbrev overlap (i k : ι) : X.Opens := D.opens i ⊓ D.opens k

theorem overlap_eq (i k : ι) : D.overlap i k = D.opens i ⊓ D.opens k := rfl

theorem overlap_le_left (i k : ι) : D.overlap i k ≤ D.opens i := inf_le_left

theorem overlap_le_right (i k : ι) : D.overlap i k ≤ D.opens k := inf_le_right

def transition (i k : ι) : Γ(X, D.opens i ⊓ D.opens k) :=
  X.presheaf.map (homOfLE (show D.opens i ⊓ D.opens k ≤ D.opens i from inf_le_left)).op (D.ratio i k)

theorem overlap_basicOpen_ratio (i k j : ι) :
    X.basicOpen (X.presheaf.map
      (homOfLE (show D.opens i ⊓ D.opens k ≤ D.opens i from inf_le_left)).op (D.ratio i j)) =
      (D.opens i ⊓ D.opens k) ⊓ D.opens j := by
  rw [Scheme.basicOpen_res, D.basicOpen_ratio]
  ac_rfl

end CoordinateSectionCover

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.SectionCover
