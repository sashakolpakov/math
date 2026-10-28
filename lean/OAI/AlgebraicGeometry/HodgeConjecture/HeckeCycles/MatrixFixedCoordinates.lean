import Mathlib

/-! # Matrix Fixed Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixFixedCoordinates.CM

noncomputable section

/-! Fixed coordinates determine the complete matrix after applying
a coefficient homomorphism. -/

open scoped Classical

theorem identity {R S V J : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V] [Fintype J] [DecidableEq J]
    (e : V ≃ₗ[R] (J → R)) (g : V →ₗ[R] V) (f : R →+* S)
    (h : ∀ x : V, ∀ i : J, f (e (g x) i) = f (e x i)) :
    (fun i j => f (e (g (e.symm (Pi.single j 1))) i)) = (1 : Matrix J J S) := by
  apply Matrix.ext
  intro i j
  refine (h _ i).trans ?_
  refine (congrArg (fun x : J → R => f (x i)) (e.apply_symm_apply (Pi.single j 1))).trans ?_
  by_cases hij : i = j
  · subst j
    simp only [Pi.single_eq_same, map_one, Matrix.one_apply_eq]
  · simp only [Pi.single_eq_of_ne hij, map_zero, Matrix.one_apply_ne hij]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatrixFixedCoordinates.CM
