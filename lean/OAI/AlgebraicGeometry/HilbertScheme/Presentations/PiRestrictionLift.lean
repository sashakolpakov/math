import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionEquiv

/-! # Pi Restriction Lift -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionLift

noncomputable section

/-! Restriction of a dependent product along an embedding has a lift supported on the image. -/

universe u v w t z

variable {R : Type u} [CommRing R] {ι : Type v} [Nonempty ι] {κ : Type w}
variable (A : ι → Type t) (B : κ → Type z)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]

theorem piRestrictionLinear_lift_supported (e : ι ↪ κ) (E : ∀ i, B (e i) ≃ₗ[R] A i)
    (x : ∀ i, A i) :
    ∃ y : ∀ j, B j, PiRestrictionEquiv.piRestrictionLinear A B e E y = x ∧ ∀ j, j ∉ Set.range e → y j = 0 := by
  classical
  obtain ⟨g, hg⟩ := e.injective.hasLeftInverse
  let y : ∀ j, B j := fun j => if hj : e (g j) = j then hj ▸ ((E (g j)).symm (x (g j))) else 0
  refine ⟨y, ?_, ?_⟩
  · funext i
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
  · intro j hj
    have h : ¬ e (g j) = j := fun h => hj ⟨g j, h⟩
    exact dite_eq_right h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionLift
