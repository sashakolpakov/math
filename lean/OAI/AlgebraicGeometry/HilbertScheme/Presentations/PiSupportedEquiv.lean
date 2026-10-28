import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiRestrictionLift

/-! # Pi Supported Equiv -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiSupportedEquiv

noncomputable section

/-! A dependent product supported on an embedded index set is the product over that index set. -/

universe u v w t z

variable {R : Type u} [CommRing R] {ι : Type v} [Nonempty ι] {κ : Type w}
variable (A : ι → Type t) (B : κ → Type z)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module R (A i)]
variable [∀ j, AddCommGroup (B j)] [∀ j, Module R (B j)]

def piImageSupport (e : ι ↪ κ) : Submodule R (∀ j, B j) where
  carrier := {y | ∀ j, j ∉ Set.range e → y j = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' {x y} hx hy j hj := by
    change x j + y j = 0
    rw [hx j hj, hy j hj, add_zero]
  smul_mem' r y hy j hj := by
    change r • y j = 0
    rw [hy j hj, smul_zero]

def piSupportedRestrictionEquiv (e : ι ↪ κ) (E : ∀ i, B (e i) ≃ₗ[R] A i) :
    piImageSupport (R := R) B e ≃ₗ[R] ∀ i, A i :=
  LinearEquiv.ofBijective ((PiRestrictionEquiv.piRestrictionLinear A B e E).comp (piImageSupport (R := R) B e).subtype) (by
    constructor
    · intro x y hxy
      apply Subtype.ext
      funext j
      by_cases hj : j ∈ Set.range e
      · obtain ⟨i, rfl⟩ := hj
        exact (E i).injective (congrFun hxy i)
      · exact (x.property j hj).trans (y.property j hj).symm
    · intro x
      obtain ⟨y, hy, hs⟩ := PiRestrictionLift.piRestrictionLinear_lift_supported A B e E x
      exact ⟨⟨y, hs⟩, hy⟩)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.PiSupportedEquiv
