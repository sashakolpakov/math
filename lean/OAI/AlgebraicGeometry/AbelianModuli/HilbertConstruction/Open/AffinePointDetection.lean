import Mathlib.AlgebraicGeometry.ResidueField

/-! # Affine Point Detection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AffinePointDetection

noncomputable section

/-! Open subsets are determined by which affine scheme maps land in them. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem opens_eq_of_affine_range_iff {X : Scheme.{u}} (U V : X.Opens)
    (h : ∀ (R : CommRingCat.{u}) (x : Spec R ⟶ X),
      Set.range x ⊆ (U : Set X) ↔ Set.range x ⊆ (V : Set X)) : U = V := by
  apply TopologicalSpace.Opens.ext
  apply Set.ext
  intro p
  have hp := h (X.residueField p) (X.fromSpecResidueField p)
  rw [Scheme.range_fromSpecResidueField, Set.singleton_subset_iff, Set.singleton_subset_iff] at hp
  exact hp

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.AffinePointDetection
