import OAI.AlgebraicGeometry.Comparison.Betti.Projective.Intersections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoordinateExtensions

/-! # Intersection Inclusions -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionInclusions.Dolbeault

noncomputable section

/-! Original open inclusions for nested projective Čech intersections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem projectiveAlgebraicIntersection_antitone (n : ℕ) {s t : Finset (Fin (n + 1))}
    (h : s ⊆ t) : Intersections.Dolbeault.projectiveAlgebraicIntersection n t ≤ Intersections.Dolbeault.projectiveAlgebraicIntersection n s := by
  intro x hx
  apply (Intersections.Dolbeault.mem_projectiveAlgebraicIntersection n s x).mpr
  intro i hi
  exact (Intersections.Dolbeault.mem_projectiveAlgebraicIntersection n t x).mp hx i (h hi)

theorem projectiveAlgebraicIntersection_le_overlap (n : ℕ) (s : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ s) (k : Fin (n + 1)) (hk : k ∈ s) :
    Intersections.Dolbeault.projectiveAlgebraicIntersection n s ≤ SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap (R := ℂ) i k := by
  rw [SheafCohomology.Projective.CoordinateExtensions.MvPolynomial.coordinateOpenOverlap_eq]
  exact le_inf (Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s i hi) (Intersections.Dolbeault.projectiveAlgebraicIntersection_le n s k hk)

theorem projectiveTupleRange_coface_subset (n q : ℕ) (t : Fin (q + 2) → Fin (n + 1))
    (k : Fin (q + 2)) : Finset.univ.image (t ∘ k.succAbove) ⊆ Finset.univ.image t := by
  intro i hi
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_image.mpr ⟨k.succAbove a, Finset.mem_univ _, rfl⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.IntersectionInclusions.Dolbeault
