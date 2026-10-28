import OAI.NumberTheory.Quaternion.Arithmetic.PrimeLocalIntegral
import Mathlib.Data.Nat.ChineseRemainder

/-! # Prime Mask Exponentials -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.PrimeMaskExponentials

noncomputable section

section

/-! Chinese remainders give sequences of nonnegative integers converging
to one at a chosen residue characteristic and to zero at the others. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem natCast_sub_norm_le_of_modEq (v : HeightOneSpectrum (𝓞 F))
    {a b j : ℕ} (h : a ≡ b [MOD LocalCompletion.residuePrime v ^ j]) :
    ‖(a : v.adicCompletion F) - (b : v.adicCompletion F)‖ ≤
      ‖(LocalCompletion.residuePrime v : v.adicCompletion F)‖ ^ j := by
  obtain ⟨z, hz⟩ := h.symm.dvd
  have he : (a : v.adicCompletion F) - (b : v.adicCompletion F) =
      (LocalCompletion.residuePrime v : v.adicCompletion F) ^ j * (z : v.adicCompletion F) := by
    have hh := congrArg (Int.castRingHom (v.adicCompletion F)) hz
    simpa only [map_sub, map_mul, Int.coe_castRingHom, Int.cast_pow,
      Int.cast_natCast, Nat.cast_pow] using hh
  rw [he, norm_mul, norm_pow]
  exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) (PrimeLocalIntegral.intCast_norm_le_one v z)

theorem natCast_tendsto_of_modEq_powers (v : HeightOneSpectrum (𝓞 F))
    (m : ℕ → ℕ) (a : ℕ) (h : ∀ j, m j ≡ a [MOD LocalCompletion.residuePrime v ^ j]) :
    Tendsto (fun j => (m j : v.adicCompletion F)) atTop (𝓝 (a : v.adicCompletion F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun j => norm_nonneg _) (fun j => natCast_sub_norm_le_of_modEq v (h j))
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _)
    ((LocalCompletion.natCast_norm_lt_one_iff v _).mpr dvd_rfl)

theorem exists_natCast_prime_mask_sequence {ι : Type*} [Fintype ι]
    (v : ι → HeightOneSpectrum (𝓞 F)) (q : ℕ) :
    ∃ m : ℕ → ℕ, ∀ i,
      Tendsto (fun j => (m j : (v i).adicCompletion F)) atTop
        (𝓝 (if LocalCompletion.residuePrime (v i) = q then 1 else 0)) := by
  let P := Finset.univ.image (fun i => LocalCompletion.residuePrime (v i))
  have hP : ∀ p ∈ P, p.Prime := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact LocalCompletion.residuePrime_prime (v i)
  let a : ℕ → ℕ := fun p => if p = q then 1 else 0
  have hex (j : ℕ) : ∃ m : ℕ, ∀ p ∈ P, m ≡ a p [MOD p ^ j] := by
    let r := Nat.chineseRemainderOfFinset a (fun p => p ^ j) P
      (fun p hp => pow_ne_zero _ (hP p hp).ne_zero)
      (by
        intro p hp r hr hpr
        exact Nat.coprime_pow_primes j j (hP p hp) (hP r hr) hpr)
    exact ⟨r.val, r.property⟩
  choose m hm using hex
  refine ⟨m, fun i => ?_⟩
  have hi : LocalCompletion.residuePrime (v i) ∈ P := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have ht := natCast_tendsto_of_modEq_powers (v i) m (a (LocalCompletion.residuePrime (v i)))
    (fun j => hm j _ hi)
  simpa only [a, apply_ite, Nat.cast_one, Nat.cast_zero] using ht

end

/-! Closed subgroups of a finite local product contain the residue-prime
blocks of sufficiently small exponential elements. Integer powers and
Chinese remainders separate the blocks. -/

open scoped Classical _root_.NumberField
open IsDedekindDomain NormedSpace Filter _root_.Topology

variable {F : Type} [Field F] [NumberField F]

theorem prime_mask_exp_mem_closed_submonoid {ι : Type*} [Fintype ι]
    (v : ι → HeightOneSpectrum (𝓞 F)) {A : ι → Type*}
    [∀ i, NormedRing (A i)] [∀ i, NormedAlgebra ((v i).adicCompletion F) (A i)]
    [∀ i, CompleteSpace (A i)]
    (H : Submonoid (∀ i, A i)) (hH : IsClosed (H : Set (∀ i, A i)))
    (X : ∀ i, A i)
    (hX : ∀ i, X i ∈ Metric.eball 0 (expSeries ((v i).adicCompletion F) (A i)).radius)
    (hexp : (fun i => exp (X i)) ∈ H) (q : ℕ) :
    (fun i => if LocalCompletion.residuePrime (v i) = q then exp (X i) else 1) ∈ H := by
  obtain ⟨m, hm⟩ := exists_natCast_prime_mask_sequence v q
  let Y : ∀ i, A i := fun i => if LocalCompletion.residuePrime (v i) = q then exp (X i) else 1
  have ht : Tendsto (fun j => fun i => exp ((m j : (v i).adicCompletion F) • X i))
      atTop (𝓝 Y) := by
    apply tendsto_pi_nhds.mpr
    intro i
    let : CharZero ((v i).adicCompletion F) := Algebra.charZero_of_charZero F _
    have hs := (hm i).smul (tendsto_const_nhds (x := X i))
    have hb : (if LocalCompletion.residuePrime (v i) = q then (1 : (v i).adicCompletion F) else 0) • X i ∈
        Metric.eball 0 (expSeries ((v i).adicCompletion F) (A i)).radius := by
      split_ifs
      · simpa using hX i
      · simpa using LocalCompletion.finite_expSeries_radius_pos (v i) (A i)
    have he := (analyticAt_exp_of_mem_ball _ hb).continuousAt.tendsto.comp hs
    simpa only [Y, ite_smul, one_smul, zero_smul, apply_ite, exp_zero, Function.comp_def] using he
  apply hH.mem_of_tendsto ht
  apply Filter.Eventually.of_forall
  intro j
  have he : (fun i => exp ((m j : (v i).adicCompletion F) • X i)) =
      (fun i => exp (X i)) ^ m j := by
    funext i
    rw [Nat.cast_smul_eq_nsmul, PrimeLocalIntegral.finite_exp_nsmul (v i) _ (hX i)]
    rfl
  rw [he]
  exact H.pow_mem hexp _

end

end OAI.NumberTheory.Quaternion.Arithmetic.PrimeMaskExponentials
