import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.RingTheory.Ideal.Span

/-! # Inverse Ideal Eq -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal

noncomputable section

/-! The inverse fractional module of an ideal and the inverse of a principal generator. -/

variable {R F : Type*} [CommRing R] [Field F] [Algebra R F]

def module (I : Ideal R) : Submodule R F where
  carrier := {q | ∀ a ∈ I, ∃ b : R, q * algebraMap R F a = algebraMap R F b}
  zero_mem' a _ := ⟨0, by simp⟩
  add_mem' := by
    intro q r hq hr a ha
    obtain ⟨b, hb⟩ := hq a ha
    obtain ⟨c, hc⟩ := hr a ha
    exact ⟨b + c, by rw [add_mul, hb, hc, map_add]⟩
  smul_mem' := by
    intro a q hq b hb
    obtain ⟨c, hc⟩ := hq b hb
    exact ⟨a * c, by rw [Algebra.smul_def, mul_assoc, hc, map_mul]⟩

theorem one_mem (I : Ideal R) : (1 : F) ∈ module I := by
  intro a _
  exact ⟨a, one_mul _⟩

theorem mem_span_iff (a : R) (q : F) :
    q ∈ module (Ideal.span {a}) ↔ ∃ b : R, q * algebraMap R F a = algebraMap R F b := by
  constructor
  · intro h
    exact h a (Ideal.subset_span (Set.mem_singleton a))
  · rintro ⟨b, hb⟩ c hc
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp hc
    refine ⟨b * d, ?_⟩
    rw [hd, map_mul, ← mul_assoc, hb, map_mul]

theorem span_eq (a : R) (ha : algebraMap R F a ≠ 0) :
    module (Ideal.span {a}) = Submodule.span R {(algebraMap R F a)⁻¹} := by
  ext q
  rw [mem_span_iff, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [Algebra.smul_def]
    rw [← hb, mul_assoc, mul_inv_cancel₀ ha, mul_one]
  · rintro ⟨b, hb⟩
    refine ⟨b, ?_⟩
    rw [Algebra.smul_def] at hb
    rw [← hb, mul_assoc, inv_mul_cancel₀ ha, mul_one]

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.InverseIdealEq.Construction.InverseIdeal
