import Mathlib.LinearAlgebra.Pi

/-! # Pi Restriction Equiv -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionEquiv

noncomputable section

/-! Restricting a dependent product along an embedding discards only zero modules. -/

universe u v w t z

variable {R : Type u} [CommRing R] {ι : Type v} [Nonempty ι] {κ : Type w}
variable (A : ι → Type t) (B : κ → Type z)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]

def piRestrictionLinear (e : ι ↪ κ) (E : ∀ i, B (e i) ≃ₗ[R] A i) :
    (∀ j, B j) →ₗ[R] ∀ i, A i where
  toFun x i := E i (x (e i))
  map_add' x y := by funext i; exact map_add (E i) (x (e i)) (y (e i))
  map_smul' r x := by funext i; exact map_smul (E i) r (x (e i))

theorem piRestrictionLinear_bijective (e : ι ↪ κ) (E : ∀ i, B (e i) ≃ₗ[R] A i)
    (hzero : ∀ j : κ, j ∉ Set.range e → Subsingleton (B j)) :
    Function.Bijective (piRestrictionLinear A B e E) := by
  classical
  constructor
  · intro x y hxy
    funext j
    by_cases hj : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hj
      exact (E i).injective (congrFun hxy i)
    · exact @Subsingleton.elim (B j) (hzero j hj) (x j) (y j)
  · intro x
    obtain ⟨g, hg⟩ := e.injective.hasLeftInverse
    let y : ∀ j, B j := fun j => if hj : e (g j) = j then hj ▸ ((E (g j)).symm (x (g j))) else 0
    refine ⟨y, ?_⟩
    funext i
    have hy : y (e i) = (E i).symm (x i) := by
      have ht (j k : ι) (h : j = k) :
          (congrArg e h) ▸ ((E j).symm (x j)) = (E k).symm (x k) := by
        subst k
        rfl
      dsimp only [y]
      rw [dite_eq_left (congrArg e (hg i))]
      exact ht (g (e i)) i (hg i)
    change E i (y (e i)) = x i
    rw [hy, LinearEquiv.apply_symm_apply]

def piRestrictionEquiv (e : ι ↪ κ) (E : ∀ i, B (e i) ≃ₗ[R] A i)
    (hzero : ∀ j : κ, j ∉ Set.range e → Subsingleton (B j)) :
    (∀ j, B j) ≃ₗ[R] ∀ i, A i :=
  LinearEquiv.ofBijective (piRestrictionLinear A B e E) (piRestrictionLinear_bijective A B e E hzero)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionEquiv
