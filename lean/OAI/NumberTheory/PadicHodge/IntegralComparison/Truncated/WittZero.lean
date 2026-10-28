import OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.Witt
import Mathlib.RingTheory.WittVector.Complete

/-! # Witt Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittZero

noncomputable section

/-!
# IntegralComparison: the zeroth bounded Witt base is the original residue field
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p] [PerfectRing k p]

def residueEquiv : Witt.Ring p k 0 ≃+* k :=
  (Ideal.quotEquivOfEq (pow_one (Ideal.span {(p : WittVector p k)}))).trans
    (WittVector.quotientPEquiv (p := p) (k := k))

theorem residueEquiv_eq_reduction : (residueEquiv p k).toRingHom = Witt.reduction p k 0 := by
  apply RingHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem ideal_eq_bot : Witt.ideal p k 0 = ⊥ := by
  rw [← Witt.reduction_kernel p k 0, ← residueEquiv_eq_reduction p k]
  exact (RingHom.ker_eq_bot_iff_eq_zero _).mpr (fun x hx => (residueEquiv p k).injective
    (hx.trans (residueEquiv p k).map_zero.symm))

theorem reduction_bijective : Function.Bijective (Witt.reduction p k 0) := by
  rw [← residueEquiv_eq_reduction p k]
  exact (residueEquiv p k).bijective

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Truncated.WittZero
