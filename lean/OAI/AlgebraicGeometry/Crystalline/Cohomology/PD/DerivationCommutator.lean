import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.OneForms
import Mathlib.RingTheory.Derivation.Lie

/-! # Derivation Commutator -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationCommutator.PDDerivationCommutator

noncomputable section

/-!
# Commutators of divided-power derivations

The commutator of two PD-compatible derivations is again PD-compatible.
This lets uniqueness of extension detect commuting coordinate derivatives.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal A) (δ : DividedPowers I) (d e : Derivation R A A)
  (hd : ∀ n x, x ∈ I → d (δ.dpow (n + 1) x) = δ.dpow n x * d x)
  (he : ∀ n x, x ∈ I → e (δ.dpow (n + 1) x) = δ.dpow n x * e x)

include hd he in
theorem commutator_dpow (n : ℕ) {x : A} (hx : x ∈ I) :
    ⁅d, e⁆ (δ.dpow (n + 1) x) = δ.dpow n x * ⁅d, e⁆ x := by
  cases n with
  | zero => simp only [Nat.zero_add, δ.dpow_one hx, δ.dpow_zero hx, one_mul]
  | succ n =>
    simp only [Derivation.commutator_apply, hd (n + 1) x hx, he (n + 1) x hx,
      Derivation.leibniz, hd n x hx, he n x hx, smul_eq_mul]
    ring

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.DerivationCommutator.PDDerivationCommutator
