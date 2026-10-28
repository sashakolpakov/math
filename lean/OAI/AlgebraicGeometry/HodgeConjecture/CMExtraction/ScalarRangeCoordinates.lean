import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi

/-! # Scalar Range Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarRangeCoordinates.TestTransport

noncomputable section

/-! In basis coordinates, the scalar-subring span is exactly the set
of vectors whose coordinates lie in the scalar ring's image. -/

open scoped Classical

variable {R K J : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [Fintype J] [DecidableEq J]

theorem span_standard_vectors_iff (x : J → K) :
    x ∈ Submodule.span R (Set.range (fun j : J => (Pi.single j 1 : J → K))) ↔
      ∀ j, ∃ r : R, algebraMap R K r = x j := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        intro k
        by_cases hjk : j = k
        · subst k
          exact ⟨1, by simp⟩
        · exact ⟨0, by simp [Pi.single_eq_of_ne (Ne.symm hjk)]⟩
    | zero => intro j; exact ⟨0, map_zero _⟩
    | add y z _ _ hy hz =>
        intro j
        obtain ⟨r, hr⟩ := hy j
        obtain ⟨s, hs⟩ := hz j
        exact ⟨r + s, by rw [map_add, hr, hs]; rfl⟩
    | smul r y _ hy =>
        intro j
        obtain ⟨s, hs⟩ := hy j
        exact ⟨r * s, by rw [map_mul, hs]; exact (Algebra.smul_def _ _).symm⟩
  · intro hx
    choose r hr using hx
    have he : (∑ j, r j • (Pi.single j 1 : J → K)) = x := by
      funext j
      simp [Pi.single_apply, Algebra.smul_def, hr]
    rw [← he]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
  (e : V ≃ₗ[K] (J → K)) (b : J → V) (hb : ∀ j, e (b j) = Pi.single j 1)

include hb in
theorem span_basis_scalar_coordinates (x : V) :
    x ∈ Submodule.span R (Set.range b) ↔ ∀ j, ∃ r : R, algebraMap R K r = e x j := by
  have hm : (Submodule.span R (Set.range b)).map (e.restrictScalars R).toLinearMap =
      Submodule.span R (Set.range (fun j : J => (Pi.single j 1 : J → K))) := by
    rw [Submodule.map_span, ← Set.range_comp]
    congr 2
    funext j
    exact hb j
  rw [← span_standard_vectors_iff (R := R) (e x), ← hm]
  constructor
  · intro hx
    exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, he⟩
    exact e.injective he ▸ hy

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarRangeCoordinates.TestTransport
