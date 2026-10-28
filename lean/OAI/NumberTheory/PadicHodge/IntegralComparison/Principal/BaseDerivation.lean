import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.RingTheory.Derivation.Basic

/-! # Base Derivation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseDerivation

noncomputable section

/-! Relative derivations respect divided powers on a principal ideal extended from the base. -/

universe u v w

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  (r : R) (δR : DividedPowers (Ideal.span {r}))
  (δA : DividedPowers (Ideal.span {algebraMap R A r}))
  (hδ : DividedPowers.IsDPMorphism δR δA (algebraMap R A))
  (M : Type w) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  (D : Derivation R A M)

omit [IsScalarTower R A M] in
include hδ in
theorem base_constant (m : ℕ) : D (δA.dpow m (algebraMap R A r)) = 0 := by
  rw [hδ.dpow_comp r (Ideal.subset_span (Set.mem_singleton r)), D.map_algebraMap]

theorem recurrence (m : ℕ) : (m + 1 : A) * δA.dpow (m + 1) (algebraMap R A r) =
    algebraMap R A r * δA.dpow m (algebraMap R A r) := by
  have h := δA.mul_dpow (m := 1) (n := m) (Ideal.subset_span (Set.mem_singleton (algebraMap R A r)))
  simpa only [δA.dpow_one (Ideal.subset_span (Set.mem_singleton (algebraMap R A r))),
    Nat.choose_one_right, Nat.add_comm 1 m, Nat.cast_add, Nat.cast_one] using h.symm

omit [IsScalarTower R A M] in
include hδ in
theorem compatible (m : ℕ) (x : A) (hx : x ∈ Ideal.span {algebraMap R A r}) :
    D (δA.dpow (m + 1) x) = δA.dpow m x • D x := by
  obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hx
  have hb : algebraMap R A r ∈ Ideal.span {algebraMap R A r} := Ideal.subset_span (Set.mem_singleton _)
  rw [δA.dpow_mul_right hb, δA.dpow_mul_right hb, D.leibniz,
    base_constant R A r δR δA hδ M D, smul_zero, add_zero,
    D.leibniz, D.map_algebraMap, smul_zero, add_zero, D.leibniz_pow]
  simp only [Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul A, smul_smul, Nat.cast_add, Nat.cast_one]
  congr 1
  calc
    δA.dpow (m + 1) (algebraMap R A r) * ((m + 1 : A) * z ^ m) =
        ((m + 1 : A) * δA.dpow (m + 1) (algebraMap R A r)) * z ^ m := by ring
    _ = (δA.dpow m (algebraMap R A r) * z ^ m) * algebraMap R A r := by
      rw [recurrence R A r δA]
      ring

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Principal.BaseDerivation
