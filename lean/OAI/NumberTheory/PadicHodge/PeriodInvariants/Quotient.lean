import OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicSeparation
import Mathlib.RingTheory.AdicCompletion.Exactness

/-! # Quotient -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.Quotient

noncomputable section

/-!
# Complete integral lattices in the finite theta quotients

Cancellation modulo p makes multiplication by a power of xi strict for the
p-adic filtration. Its image is therefore closed, and the corresponding
quotient is p-adically complete even though A_inf is not Noetherian.
-/

section General

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

theorem precomplete_of_surjective (I : Ideal R) [IsPrecomplete I M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : IsPrecomplete I N := by
  apply AdicCompletion.of_surjective_iff.mp
  intro x
  obtain ⟨y, hy⟩ := AdicCompletion.map_surjective I hf x
  obtain ⟨z, rfl⟩ := AdicCompletion.of_surjective I M y
  exact ⟨f z, (AdicCompletion.map_of I f z).symm.trans hy⟩

variable (r ξ : R) [IsAdicComplete (Ideal.span {r}) R]

theorem principal_closed (hreg : ∀ (n : ℕ) (a : R), r ^ n ∣ ξ * a → r ^ n ∣ a)
    (a : R) (ha : ∀ n : ℕ, ∃ b : R, r ^ n ∣ a - ξ * b) : ξ ∣ a := by
  choose b hb using ha
  have hseq : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD ((Ideal.span {r}) ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    apply hreg
    have hn := dvd_trans (pow_dvd_pow r hmn) (hb n)
    have hd := dvd_sub hn (hb m)
    convert hd using 1
    ring
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {r}) b hseq
  refine ⟨L, ?_⟩
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := Ideal.span {r})
  intro n
  rw [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hn : r ^ n ∣ b n - L := by
    simpa only [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hL n
  have hd := dvd_add (hb n) (dvd_mul_of_dvd_right hn ξ)
  convert hd using 1
  ring

theorem principal_quotient_separated
    (hreg : ∀ (n : ℕ) (a : R), r ^ n ∣ ξ * a → r ^ n ∣ a) :
    IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) r}) (R ⧸ Ideal.span {ξ}) := by
  constructor
  intro x hx
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply principal_closed r ξ hreg a
  intro n
  have hn : (Ideal.Quotient.mk (Ideal.span {ξ}) r) ^ n ∣
      Ideal.Quotient.mk (Ideal.span {ξ}) a := by
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hx n
  obtain ⟨q, hq⟩ := hn
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
  have hz : Ideal.Quotient.mk (Ideal.span {ξ}) (a - r ^ n * c) = 0 := by
    rw [map_sub, map_mul, map_pow, hq, sub_self]
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  exact ⟨b, c, by rw [← hb]; ring⟩

theorem principal_quotient_complete
    (hreg : ∀ (n : ℕ) (a : R), r ^ n ∣ ξ * a → r ^ n ∣ a) :
    IsAdicComplete (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) r})
      (R ⧸ Ideal.span {ξ}) := by
  let _ : IsHausdorff (Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) r})
      (R ⧸ Ideal.span {ξ}) := principal_quotient_separated r ξ hreg
  have hp : IsPrecomplete (Ideal.span {r}) (R ⧸ Ideal.span {ξ}) :=
    precomplete_of_surjective (Ideal.span {r}) (Ideal.span {ξ}).mkQ
      (Submodule.mkQ_surjective _)
  have hp' := (IsPrecomplete.map_algebraMap_iff
    (I := Ideal.span {r}) (S := R ⧸ Ideal.span {ξ}) (M := R ⧸ Ideal.span {ξ})).mpr hp
  have he : (Ideal.span {r}).map (algebraMap R (R ⧸ Ideal.span {ξ})) =
      Ideal.span {Ideal.Quotient.mk (Ideal.span {ξ}) r} := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [he] at hp'
  exact { toIsHausdorff := inferInstance, toIsPrecomplete := hp' }

end General

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing OAI.NumberTheory.PadicHodge.PeriodInvariants.ThetaKernel OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing.TiltDivisibility OAI.NumberTheory.PadicHodge.PeriodInvariants.AdicSeparation

variable (p : ℕ) [Fact p.Prime]

theorem p_dvd_of_xi_pow_mul (m : ℕ) (a : PeriodRing.Ainf p)
    (h : (p : PeriodRing.Ainf p) ∣ ThetaKernel.xi p ^ m * a) : (p : PeriodRing.Ainf p) ∣ a := by
  apply Ideal.mem_span_singleton.mp
  apply (WittVector.mem_span_p_iff_coeff_zero_eq_zero a).mpr
  have hc := (WittVector.mem_span_p_iff_coeff_zero_eq_zero (ThetaKernel.xi p ^ m * a)).mp
    (Ideal.mem_span_singleton.mpr h)
  change WittVector.constantCoeff (ThetaKernel.xi p ^ m * a) = 0 at hc
  rw [map_mul, map_pow] at hc
  change (ThetaKernel.xi p).coeff 0 ^ m * a.coeff 0 = 0 at hc
  rw [ThetaKernel.xi_coeff_zero] at hc
  exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero m (ThetaKernel.pTilt_ne_zero p))

theorem p_pow_dvd_of_xi_pow_mul (n m : ℕ) (a : PeriodRing.Ainf p)
    (h : (p : PeriodRing.Ainf p) ^ n ∣ ThetaKernel.xi p ^ m * a) : (p : PeriodRing.Ainf p) ^ n ∣ a := by
  induction n generalizing a with
  | zero => simp only [pow_zero, one_dvd]
  | succ n ih =>
    obtain ⟨b, hb⟩ := p_dvd_of_xi_pow_mul p m a
      (dvd_trans (dvd_pow_self (p : PeriodRing.Ainf p) (Nat.succ_ne_zero n)) h)
    obtain ⟨c, hc⟩ := h
    have he : (p : PeriodRing.Ainf p) * (ThetaKernel.xi p ^ m * b) = (p : PeriodRing.Ainf p) * ((p : PeriodRing.Ainf p) ^ n * c) := by
      calc
        (p : PeriodRing.Ainf p) * (ThetaKernel.xi p ^ m * b) = ThetaKernel.xi p ^ m * a := by rw [hb]; ring
        _ = (p : PeriodRing.Ainf p) ^ (n + 1) * c := hc
        _ = _ := by rw [pow_succ']; ring
    have hd := mul_left_cancel₀
      (show (p : PeriodRing.Ainf p) ≠ 0 from Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he
    obtain ⟨d, hd⟩ := ih b ⟨c, hd⟩
    refine ⟨d, ?_⟩
    rw [hb, hd, pow_succ']
    ring

/-- Integral finite theta quotients are p-adically complete. -/
instance thetaPowerQuotient_complete (m : ℕ) :
    IsAdicComplete (Ideal.span {(p : PeriodRing.Ainf p ⧸ Ideal.span {ThetaKernel.xi p ^ m})})
      (PeriodRing.Ainf p ⧸ Ideal.span {ThetaKernel.xi p ^ m}) := by
  have h := principal_quotient_complete (p : PeriodRing.Ainf p) (ThetaKernel.xi p ^ m)
    (fun n a ha => p_pow_dvd_of_xi_pow_mul p n m a ha)
  simpa only [map_natCast] using h

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.Quotient
