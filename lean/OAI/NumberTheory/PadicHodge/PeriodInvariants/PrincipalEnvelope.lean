import OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel
import OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

/-! # Principal Envelope -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalEnvelope

noncomputable section

/-!
# The divided-power basis for the principal theta kernel

The actual envelope is spanned over A_inf by the divided powers of xi.
The multiplication formula has integral binomial coefficients.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel OAI.NumberTheory.PadicHodge.PeriodInvariants.Nontriviality

section Formula

variable {F : Type*} [Field F] [CharZero F]

theorem divided_power_mul (z : F) (m n : ℕ) :
    (z ^ m / (m.factorial : F)) * (z ^ n / (n.factorial : F)) =
      ((m + n).choose n : F) * (z ^ (m + n) / ((m + n).factorial : F)) := by
  rw [div_mul_div_comm, ← pow_add, ← mul_div_assoc]
  apply (div_eq_div_iff
    (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + n)))).mpr
  have h : ((m + n).choose n : F) * (m.factorial : F) * (n.factorial : F) =
      ((m + n).factorial : F) := by
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial m n
  rw [← h]
  ring

end Formula

variable (p : ℕ) [Fact p.Prime]

def xiKernel : RingHom.ker (PeriodRing.theta p) := ⟨ThetaKernel.xi p, ThetaKernel.theta_xi p⟩

def xiDividedPower (n : ℕ) : PeriodRing.AcrisZero p := PeriodRing.dividedPower p n (xiKernel p)

theorem envelope_algebraMap_coe (a : PeriodRing.Ainf p) :
    (algebraMap (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) a : FractionRing (PeriodRing.Ainf p)) =
      algebraMap (PeriodRing.Ainf p) (FractionRing (PeriodRing.Ainf p)) a := rfl

theorem envelope_pow_coe (a : PeriodRing.AcrisZero p) (n : ℕ) :
    (a ^ n : PeriodRing.AcrisZero p).val = (a : FractionRing (PeriodRing.Ainf p)) ^ n := rfl

theorem xiDividedPower_zero : xiDividedPower p 0 = 1 := PeriodRing.dividedPower_zero p (xiKernel p)

theorem xiDividedPower_mul (m n : ℕ) :
    xiDividedPower p m * xiDividedPower p n =
      ((m + n).choose n : PeriodRing.Ainf p) • xiDividedPower p (m + n) := by
  apply Subtype.val_injective
  simp only [Algebra.smul_def, Subalgebra.coe_mul,
    map_natCast, xiDividedPower, PeriodRing.dividedPower_coe, xiKernel]
  exact divided_power_mul _ m n

theorem dividedPower_eq_smul_xi (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) :
    ∃ a : PeriodRing.Ainf p, PeriodRing.dividedPower p n x = a • xiDividedPower p n := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
    (show (x : PeriodRing.Ainf p) ∈ Ideal.span {ThetaKernel.xi p} from (ThetaKernel.theta_kernel_eq_span p) ▸ x.property)
  refine ⟨a ^ n, ?_⟩
  apply Subtype.val_injective
  simp only [Algebra.smul_def, Subalgebra.coe_mul, envelope_pow_coe, envelope_algebraMap_coe,
    map_pow, xiDividedPower, PeriodRing.dividedPower_coe, xiKernel]
  rw [ha, map_mul, mul_pow]
  ring

def dividedPowerSpan : Submodule (PeriodRing.Ainf p) (PeriodRing.AcrisZero p) :=
  Submodule.span (PeriodRing.Ainf p) (Set.range (xiDividedPower p))

theorem dividedPowerSpan_mul : dividedPowerSpan p * dividedPowerSpan p ≤ dividedPowerSpan p := by
  rw [dividedPowerSpan, Submodule.span_mul_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨n, rfl⟩, rfl⟩
  change xiDividedPower p m * xiDividedPower p n ∈
    Submodule.span (PeriodRing.Ainf p) (Set.range (xiDividedPower p))
  rw [xiDividedPower_mul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m + n, rfl⟩)

theorem dividedPower_mem_span (n : ℕ) (x : RingHom.ker (PeriodRing.theta p)) :
    PeriodRing.dividedPower p n x ∈ dividedPowerSpan p := by
  obtain ⟨a, ha⟩ := dividedPower_eq_smul_xi p n x
  rw [ha]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)

/-- The concrete envelope is generated as a module by the divided powers of xi. -/
theorem dividedPowerSpan_eq_top : dividedPowerSpan p = ⊤ := by
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨x, hx⟩ := x
  change x ∈ Algebra.adjoin (PeriodRing.Ainf p) (PeriodRing.dividedPowerGenerators p) at hx
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨⟨n, a⟩, rfl⟩ := hy
    exact dividedPower_mem_span p n a
  | algebraMap a =>
    have h := Submodule.smul_mem (dividedPowerSpan p) a
      (Submodule.subset_span (show xiDividedPower p 0 ∈ Set.range (xiDividedPower p) from ⟨0, rfl⟩))
    simp only [xiDividedPower_zero, Algebra.smul_def, mul_one] at h
    convert h using 1
    apply Subtype.ext
    rfl
  | add y z hy hz ihy ihz => exact Submodule.add_mem _ ihy ihz
  | mul y z hy hz ihy ihz => exact (Submodule.mul_le.mp (dividedPowerSpan_mul p)) _ ihy _ ihz

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.PrincipalEnvelope
