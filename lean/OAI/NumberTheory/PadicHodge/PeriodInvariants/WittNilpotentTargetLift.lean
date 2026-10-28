import Mathlib.RingTheory.Perfectoid.FontaineTheta
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Witt Nilpotent Target Lift -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.WittNilpotentTargetLift

noncomputable section

/-! # Finite ghost components lift Witt vectors into a ring killed by a power of p -/

universe u v
variable (p : ℕ) [Fact p.Prime] (T : Type u) [CommRing T] [CharP T p] [PerfectRing T p]

def roots : ℕ → T →+* T
  | 0 => RingHom.id T
  | n + 1 => (roots n).comp (frobeniusEquiv T p).symm.toRingHom

theorem roots_pow (n : ℕ) (x : T) : WittNilpotentTargetLift.roots p T n x ^ (p ^ n) = x := by
  induction n generalizing x with
  | zero => simp [WittNilpotentTargetLift.roots]
  | succ n ih =>
    change (WittNilpotentTargetLift.roots p T n ((frobeniusEquiv T p).symm x)) ^ (p ^ (n + 1)) = x
    rw [pow_succ, pow_mul, ih, frobeniusEquiv_symm_pow_p]

variable {A : Type v} [CommRing A] (n : ℕ) (hn : (p : A) ^ (n + 1) = 0)

include hn

omit [Fact p.Prime] in
theorem power_eq_bot : (Ideal.span {(p : A)}) ^ (n + 1) = ⊥ := by
  rw [Ideal.span_singleton_pow, hn]
  exact Ideal.span_singleton_zero

def levelEquiv : A ⧸ (Ideal.span {(p : A)}) ^ (n + 1) ≃+* A :=
  (Ideal.quotEquivOfEq (power_eq_bot p n hn)).trans (RingEquiv.quotientBot A)

omit [Fact p.Prime] in
theorem levelEquiv_mk (x : A) :
    levelEquiv p n hn (Ideal.Quotient.mk ((Ideal.span {(p : A)}) ^ (n + 1)) x) = x := rfl

variable (f : T →+* ModP A p)

def map : WittVector p T →+* A :=
  (levelEquiv p n hn).toRingHom.comp
    ((WittVector.ghostComponentModPPow n).comp (WittVector.map (f.comp (WittNilpotentTargetLift.roots p T n))))

theorem map_teichmuller (x : T) (a : A)
    (ha : Ideal.Quotient.mk (Ideal.span {(p : A)}) a = f (WittNilpotentTargetLift.roots p T n x)) :
    WittNilpotentTargetLift.map p T n hn f (WittVector.teichmuller p x) = a ^ (p ^ n) := by
  change levelEquiv p n hn (WittVector.ghostComponentModPPow n
    (WittVector.map (f.comp (WittNilpotentTargetLift.roots p T n)) (WittVector.teichmuller p x))) = a ^ (p ^ n)
  rw [WittVector.map_teichmuller]
  change levelEquiv p n hn (WittVector.ghostComponentModPPow n
    (WittVector.teichmuller p (f (WittNilpotentTargetLift.roots p T n x)))) = a ^ (p ^ n)
  rw [← ha, ← WittVector.map_teichmuller, WittVector.ghostComponentModPPow_map_mk,
    WittVector.ghostComponent_teichmuller]
  exact levelEquiv_mk p n hn _

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.WittNilpotentTargetLift
