import OAI.AlgebraicTopology.Cohomology.Singular.CubicalEndpointFaces
import Mathlib.Data.Fintype.BigOperators

/-! # Cubical Permutation Reindex -/

namespace OAI.AlgebraicTopology.Cohomology.Singular.CubicalPermutationReindex

noncomputable section

/-!
# Reindexing permutation simplices by a deleted coordinate

For any fixed input position, deleting that position from a permutation and
recording its image is a bijection. The finite-sum formula is used to collect
the endpoint faces of cube triangulations by their actual cubical face.
-/

open scoped BigOperators

variable {n : ℕ}

/-- Insert the assignment `p ↦ q` into a permutation of the remaining labels,
using the increasing identifications of both complements. -/
def insertCubePermutation (p q : Fin (n + 1)) (τ : Equiv.Perm (Fin n)) :
    Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.insertNth p q (fun j => q.succAbove (τ j))
  invFun := Fin.insertNth q p (fun j => p.succAbove (τ.symm j))
  left_inv := by
    intro a
    by_cases ha : a = p
    · subst a
      simp only [Fin.insertNth_apply_same]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
      simp only [Fin.insertNth_apply_succAbove, Equiv.symm_apply_apply]
  right_inv := by
    intro a
    by_cases ha : a = q
    · subst a
      simp only [Fin.insertNth_apply_same]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
      simp only [Fin.insertNth_apply_succAbove, Equiv.apply_symm_apply]

@[simp]
theorem insertCubePermutation_apply_same (p q : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) : insertCubePermutation p q τ p = q := by
  exact Fin.insertNth_apply_same (α := fun _ : Fin (n + 1) => Fin (n + 1))
    p q (fun j => q.succAbove (τ j))

@[simp]
theorem insertCubePermutation_apply_succAbove (p q : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) (j : Fin n) :
    insertCubePermutation p q τ (p.succAbove j) = q.succAbove (τ j) := by
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin (n + 1) => Fin (n + 1))
    p q (fun j => q.succAbove (τ j)) j

/-- Deleting the newly inserted assignment recovers the original permutation. -/
@[simp]
theorem eraseCubePermutation_insertCubePermutation (p q : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) :
    CubicalEndpointFaces.eraseCubePermutation (insertCubePermutation p q τ) p = τ := by
  apply Equiv.ext
  intro j
  apply (finSuccAboveEquiv q).injective
  apply Subtype.ext
  change q.succAbove _ = q.succAbove _
  simpa only [insertCubePermutation_apply_same, insertCubePermutation_apply_succAbove]
    using CubicalEndpointFaces.eraseCubePermutation_succAbove (insertCubePermutation p q τ) p j

/-- Recording the deleted image and reinserting it recovers the full permutation. -/
@[simp]
theorem insertCubePermutation_eraseCubePermutation
    (σ : Equiv.Perm (Fin (n + 1))) (p : Fin (n + 1)) :
    insertCubePermutation p (σ p) (CubicalEndpointFaces.eraseCubePermutation σ p) = σ := by
  apply Equiv.ext
  intro a
  by_cases ha : a = p
  · subst a
    exact insertCubePermutation_apply_same p (σ p) _
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq ha
    rw [insertCubePermutation_apply_succAbove]
    exact CubicalEndpointFaces.eraseCubePermutation_succAbove σ p j

/-- A permutation is uniquely specified by the image of a fixed input position
and its order-preserving deletion at that position. -/
def cubePermutationEraseEquiv (p : Fin (n + 1)) :
    Equiv.Perm (Fin (n + 1)) ≃ Fin (n + 1) × Equiv.Perm (Fin n) where
  toFun σ := (σ p, CubicalEndpointFaces.eraseCubePermutation σ p)
  invFun a := insertCubePermutation p a.1 a.2
  left_inv σ := insertCubePermutation_eraseCubePermutation σ p
  right_inv a := by
    rcases a with ⟨q, τ⟩
    simp only [insertCubePermutation_apply_same,
      eraseCubePermutation_insertCubePermutation]

@[simp]
theorem cubePermutationEraseEquiv_apply (p : Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    cubePermutationEraseEquiv p σ = (σ p, CubicalEndpointFaces.eraseCubePermutation σ p) := rfl

@[simp]
theorem cubePermutationEraseEquiv_symm_apply (p q : Fin (n + 1))
    (τ : Equiv.Perm (Fin n)) :
    (cubePermutationEraseEquiv p).symm (q, τ) = insertCubePermutation p q τ := rfl

/-- Collect the permutation sum by the image of a fixed input position and the
permutation remaining after deletion. This applies to every additive commutative
monoid, including actual simplicial chain modules. -/
theorem sum_eraseCubePermutation {A : Type*} [AddCommMonoid A]
    (p : Fin (n + 1)) (F : Fin (n + 1) → Equiv.Perm (Fin n) → A) :
    (∑ σ : Equiv.Perm (Fin (n + 1)), F (σ p) (CubicalEndpointFaces.eraseCubePermutation σ p)) =
      ∑ i : Fin (n + 1), ∑ τ : Equiv.Perm (Fin n), F i τ := by
  classical
  calc
    _ = ∑ a : Fin (n + 1) × Equiv.Perm (Fin n), F a.1 a.2 :=
      (cubePermutationEraseEquiv p).sum_comp (fun a => F a.1 a.2)
    _ = _ := Fintype.sum_prod_type _

end

end OAI.AlgebraicTopology.Cohomology.Singular.CubicalPermutationReindex
