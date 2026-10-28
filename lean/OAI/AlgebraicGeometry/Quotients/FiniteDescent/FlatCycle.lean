import Mathlib.RingTheory.Flat.Equalizer

/-! # Flat Cycle -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatCycle.Construction.FlatCycleDetection

noncomputable section

/-! A functional detecting a cycle after flat scalar extension already
detects a cycle from the original module. -/

open TensorProduct
open scoped TensorProduct

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]
variable {M N P : Type u} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N] [AddCommGroup P] [Module S P]

theorem exists_cycle (d : M →ₗ[R] N) (b : (S ⊗[R] M) →ₗ[S] P)
    (x : S ⊗[R] M) (hx : d.baseChange S x = 0) (hb : b x ≠ 0) :
    ∃ m : M, d m = 0 ∧ b ((1 : S) ⊗ₜ[R] m) ≠ 0 := by
  by_contra h
  have hall : ∀ m : d.ker, b ((1 : S) ⊗ₜ[R] m.val) = 0 := by
    intro m
    by_contra hm
    exact h ⟨m.val, m.property, hm⟩
  have hz : b.comp (d.ker.subtype.baseChange S) = 0 := by
    apply LinearMap.ext
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul s m =>
      change b (s ⊗ₜ[R] m.val) = 0
      have ht : s ⊗ₜ[R] m.val = s • ((1 : S) ⊗ₜ[R] m.val) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [ht, b.map_smul, hall, smul_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
  have he := Module.Flat.ker_lTensor_eq (S := S) (M := S) d
  have hm : x ∈ (d.ker.subtype.baseChange S).range := by
    change x ∈ (AlgebraTensorModule.lTensor S S d.ker.subtype).range
    rw [← he]
    exact hx
  obtain ⟨y, rfl⟩ := hm
  exact hb (LinearMap.congr_fun hz y)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.FlatCycle.Construction.FlatCycleDetection
