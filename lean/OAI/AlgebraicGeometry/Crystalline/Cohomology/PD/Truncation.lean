import Mathlib.RingTheory.DividedPowers.SubDPIdeal
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Truncation -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation

noncomputable section

/-!
# Cohomology: nilpotent truncations of divided-power ideals

Positive ordinary powers of a divided-power ideal are stable under divided
powers. Quotienting by such a power therefore gives an actual nilpotent
divided-power thickening.
-/

open scoped Pointwise

universe u

variable (A : Type u) [CommRing A] (I : Ideal A) (δ : DividedPowers I)

/-- Multiplying a divided-power ideal by any ideal gives a sub-DP ideal. -/
theorem product_isSubDPIdeal (J : Ideal A) : DividedPowers.IsSubDPIdeal δ (I * J) := by
  have heq : I * J = Ideal.span ((I : Set A) * (J : Set A)) := by
    rw [← Ideal.span_mul_span, Ideal.span_eq, Ideal.span_eq]
  have hS : (I : Set A) * (J : Set A) ⊆ (I : Set A) := by
    rintro _ ⟨x, hx, y, _hy, rfl⟩
    exact I.mul_mem_right y hx
  rw [heq, DividedPowers.span_isSubDPIdeal_iff hS]
  intro n hn a ha
  obtain ⟨x, hx, y, hy, rfl⟩ := ha
  rw [← heq]
  change δ.dpow n (x * y) ∈ I * J
  rw [mul_comm x y, δ.dpow_mul hx]
  simpa only [mul_comm (δ.dpow n x) (y ^ n)] using
    (Ideal.mul_mem_mul (δ.dpow_mem hn hx)
      ((Ideal.pow_le_self hn) (Ideal.pow_mem_pow hy n)) : δ.dpow n x * y ^ n ∈ I * J)

theorem power_isSubDPIdeal (n : ℕ) : DividedPowers.IsSubDPIdeal δ (I ^ (n + 1)) := by
  simpa only [pow_succ'] using product_isSubDPIdeal A I δ (I ^ n)

/-- The truncated ambient ring. -/
abbrev Ring (n : ℕ) := A ⧸ I ^ (n + 1)

def ideal (n : ℕ) : Ideal (Ring A I n) := I.map (Ideal.Quotient.mk (I ^ (n + 1)))

theorem power_inf_isSubDPIdeal (n : ℕ) : DividedPowers.IsSubDPIdeal δ (I ^ (n + 1) ⊓ I) := by
  rw [inf_of_le_left (Ideal.pow_le_self (Nat.succ_ne_zero n))]
  exact power_isSubDPIdeal A I δ n

/-- The inherited divided powers on the truncated ideal. -/
def dividedPowers (n : ℕ) : DividedPowers (ideal A I n) :=
  DividedPowers.Quotient.dividedPowers δ (power_inf_isSubDPIdeal A I δ n)

theorem quotient_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δ (PDTruncation.dividedPowers A I δ n) (Ideal.Quotient.mk (I ^ (n + 1))) :=
  DividedPowers.Quotient.isDPMorphism δ (power_inf_isSubDPIdeal A I δ n)

/-- The truncated divided-power ideal is nilpotent. -/
theorem ideal_isNilpotent (n : ℕ) : IsNilpotent (ideal A I n) := by
  refine ⟨n + 1, ?_⟩
  rw [ideal, ← Ideal.map_pow, Ideal.map_quotient_self]
  rfl

variable {B : Type u} [CommRing B] (f : A →+* B) (hker : RingHom.ker f = I)

/-- Descend a reduction map through a positive power of its kernel. -/
def reduction (n : ℕ) : Ring A I n →+* B :=
  Ideal.Quotient.lift (I ^ (n + 1)) f (fun x hx => by
    change x ∈ RingHom.ker f
    rw [hker]
    exact Ideal.pow_le_self (Nat.succ_ne_zero n) hx)

@[simp]
theorem reduction_mk (n : ℕ) (a : A) :
    reduction A I f hker n (Ideal.Quotient.mk (I ^ (n + 1)) a) = f a :=
  Ideal.Quotient.lift_mk _ _ _

theorem reduction_surjective (hf : Function.Surjective f) (n : ℕ) :
    Function.Surjective (reduction A I f hker n) := by
  intro b
  obtain ⟨a, rfl⟩ := hf b
  exact ⟨Ideal.Quotient.mk (I ^ (n + 1)) a, reduction_mk A I f hker n a⟩

theorem reduction_kernel (n : ℕ) : RingHom.ker (reduction A I f hker n) = ideal A I n := by
  calc
    _ = (RingHom.ker f).map (Ideal.Quotient.mk (I ^ (n + 1))) :=
      Ideal.ker_quotient_lift (I := I ^ (n + 1)) f _
    _ = ideal A I n := by rw [hker]; rfl

theorem quotientKernel_isSubDPIdeal (n : ℕ) :
    DividedPowers.IsSubDPIdeal δ (RingHom.ker (Ideal.Quotient.mk (I ^ (n + 1))) ⊓ I) := by
  rw [Ideal.mk_ker]
  exact power_inf_isSubDPIdeal A I δ n

/-- Divided powers stated directly on the reduction kernel. -/
def kernelDividedPowers (n : ℕ) : DividedPowers (RingHom.ker (reduction A I f hker n)) :=
  DividedPowers.Quotient.OfSurjective.dividedPowers δ Ideal.Quotient.mk_surjective
    (reduction_kernel A I f hker n) (quotientKernel_isSubDPIdeal A I δ n)

theorem quotient_kernel_isDPMorphism (n : ℕ) :
    DividedPowers.IsDPMorphism δ (kernelDividedPowers A I δ f hker n)
      (Ideal.Quotient.mk (I ^ (n + 1))) :=
  DividedPowers.Quotient.OfSurjective.isDPMorphism δ Ideal.Quotient.mk_surjective
    (reduction_kernel A I f hker n) (quotientKernel_isSubDPIdeal A I δ n)

theorem kernel_isNilpotent (n : ℕ) : IsNilpotent (RingHom.ker (reduction A I f hker n)) := by
  rw [reduction_kernel]
  exact ideal_isNilpotent A I n

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation.PDTruncation
