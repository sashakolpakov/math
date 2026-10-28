import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Standard Projective Charts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts

noncomputable section

/-! The standard coordinate charts cover the actual projective spaces used by HilbertConstruction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The variables generate an ideal containing the irrelevant ideal of the standard grading. -/
theorem coordinate_irrelevant_le_span :
    (HomogeneousIdeal.irrelevant (Projective.ProjectivePresentations.coordinateGrading R n)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → Projective.ProjectivePresentations.coordinateRing R n)) := by
  classical
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (Projective.ProjectivePresentations.coordinateGrading R n)).mpr
  intro d hd p hp
  change p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → Projective.ProjectivePresentations.coordinateRing R n))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have hpoly : p.IsHomogeneous d := hp
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hz
    have he : d = 0 := (hpoly.degree_eq_sum_deg_support ha).trans
      (Finset.sum_eq_zero (fun i _ => hz i))
    exact (Nat.ne_of_gt hd) he
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

/-- The standard projective chart opens cover projective n-space. -/
theorem standardProjectiveCharts_iSup :
    (⨆ i : Fin (n + 1), Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (Projective.ProjectivePresentations.coordinateGrading R n) MvPolynomial.X (coordinate_irrelevant_le_span R n)

theorem standardProjectiveCharts_cover (x : (Projective.ProjectivePresentations.affineProjectiveSpace R n).left) :
    ∃ i : Fin (n + 1), x ∈ Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) := by
  have hx : x ∈ ⨆ i : Fin (n + 1), Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i) :=
    (standardProjectiveCharts_iSup R n).symm ▸ trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- Each standard coordinate chart is affine. -/
theorem standardProjectiveChart_isAffine (i : Fin (n + 1)) :
    IsAffineOpen (Proj.basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)) :=
  Proj.isAffineOpen_basicOpen (Projective.ProjectivePresentations.coordinateGrading R n) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X R i) Nat.zero_lt_one

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.StandardProjectiveCharts
