import OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements

/-! # Tilt Coefficients -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients

noncomputable section

/-! Construction of finite residue-field coefficients inside the concrete tilt. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaKernel OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.ThetaQuotients.TiltCompleteness
open Filter _root_.Topology
variable (p : ℕ) [Fact p.Prime]

instance tilt_primeAlgebra : Algebra (ZMod p) (PreTilt 𝓞_ℂ_[p] p) :=
  (ZMod.castHom (dvd_refl p) (PreTilt 𝓞_ℂ_[p] p)).toAlgebra

theorem tiltResidue_surjective : Function.Surjective (PrimitiveElements.tiltResidue p) := by
  intro z
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective z
  let t : Perfection 𝓞_ℂ_[p] p := ⟨fun n => (Logarithm.PeriodRings.integerRoot p)^[n] a, by
    intro n
    change ((Logarithm.PeriodRings.integerRoot p)^[n + 1] a) ^ p = (Logarithm.PeriodRings.integerRoot p)^[n] a
    rw [Function.iterate_succ_apply', Logarithm.PeriodRings.integerRoot_pow]⟩
  refine ⟨PeriodInvariants.PeriodRing.tiltMonoidEquiv p t, ?_⟩
  rw [PrimitiveElements.tiltResidue_untilt, PeriodInvariants.PeriodRing.untilt_tiltMonoidEquiv]
  exact ha

theorem tiltResidue_zero_iff_norm_lt (a : PreTilt 𝓞_ℂ_[p] p) :
    PrimitiveElements.tiltResidue p a = 0 ↔ ‖(a.untilt : ℂ_[p])‖ < 1 := by
  rw [PrimitiveElements.tiltResidue_untilt, IsLocalRing.residue_eq_zero_iff]
  erw [Valuation.mem_maximalIdeal_iff, Logarithm.PeriodRings.valuation_eq_nnnorm]
  exact_mod_cast (Iff.rfl : ‖(a.untilt : ℂ_[p])‖₊ < 1 ↔ _)

theorem tiltResidue_pFlat : PrimitiveElements.tiltResidue p (ThetaKernel.pFlat p) = 0 := by
  rw [PrimitiveElements.tiltResidue_untilt, ThetaKernel.pFlat_untilt, map_natCast, PrimitiveElements.residueCp_p_zero]

theorem small_frobenius_power (z : PreTilt 𝓞_ℂ_[p] p) (hz : PrimitiveElements.tiltResidue p z = 0)
    (d : ℕ) (hd : 0 < d) : ∃ N : ℕ, ThetaKernel.pFlat p ∣ z ^ (p ^ (d * N)) := by
  have hnorm := (tiltResidue_zero_iff_norm_lt p z).mp hz
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (z.untilt : ℂ_[p])) hnorm
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp ht).2 ‖(p : ℂ_[p])‖ (Logarithm.PeriodRings.norm_p_pos p))
  refine ⟨N, ?_⟩
  apply ThetaKernel.tilt_dvd_of_untilt_norm_le p _ (ThetaKernel.pFlat p) (ThetaKernel.pFlat_untilt_ne_zero p)
  rw [map_pow, ThetaKernel.pFlat_untilt]
  change ‖(z.untilt : ℂ_[p]) ^ (p ^ (d * N))‖ ≤ ‖(p : ℂ_[p])‖
  rw [norm_pow]
  have he : N ≤ p ^ (d * N) := (Nat.le_mul_of_pos_left N hd).trans
    (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le
  exact (pow_le_pow_of_le_one (norm_nonneg _) hnorm.le he).trans (hN N le_rfl).le

theorem integral_tilt_residue_injective {x y : PreTilt 𝓞_ℂ_[p] p}
    (hx : IsIntegral (ZMod p) x) (hy : IsIntegral (ZMod p) y)
    (hres : PrimitiveElements.tiltResidue p x = PrimitiveElements.tiltResidue p y) : x = y := by
  apply sub_eq_zero.mp
  by_contra hxy
  have hu := (hx.sub hy).isUnit hxy
  apply (hu.map (PrimitiveElements.tiltResidue p)).ne_zero
  rw [map_sub, hres, sub_self]

theorem exists_finite_residue_lift (a : PrimitiveElements.ResidueCp p) (d : ℕ) (hd : 0 < d)
    (ha : a ^ (p ^ d) = a) :
    ∃ b : PreTilt 𝓞_ℂ_[p] p, IsIntegral (ZMod p) b ∧ PrimitiveElements.tiltResidue p b = a := by
  obtain ⟨x, hx⟩ := tiltResidue_surjective p a
  have hz : PrimitiveElements.tiltResidue p (x ^ (p ^ d) - x) = 0 := by rw [map_sub, map_pow, hx, ha, sub_self]
  obtain ⟨N, hN⟩ := small_frobenius_power p _ hz d hd
  let x₀ := x ^ (p ^ (d * N))
  have hx₀ : PrimitiveElements.tiltResidue p x₀ = a := by
    have he (m : ℕ) : a ^ ((p ^ d) ^ m) = a := by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ, pow_mul, ih, ha]
    change PrimitiveElements.tiltResidue p (x ^ (p ^ (d * N))) = a
    rw [map_pow, hx, pow_mul]
    exact he N
  let g : Polynomial (PreTilt 𝓞_ℂ_[p] p) := Polynomial.X ^ (p ^ d) - Polynomial.X
  have hm : g.Monic := by
    apply Polynomial.monic_X_pow_sub
    rw [Polynomial.degree_X]
    exact WithBot.coe_lt_coe.mpr (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  have hroot : g.eval x₀ ∈ Ideal.span {ThetaKernel.pFlat p} := by
    apply Ideal.mem_span_singleton.mpr
    have he : g.eval x₀ = (x ^ (p ^ d) - x) ^ (p ^ (d * N)) := by
      dsimp only [g, x₀]
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
      rw [sub_pow_char_pow]
      rw [pow_right_comm]
    rw [he]
    exact hN
  have hg' : g.derivative = -1 := by
    simp only [g, Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_X,
      Nat.cast_pow, CharP.cast_eq_zero, zero_pow hd.ne', Polynomial.C_0, zero_mul, zero_sub]
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {ThetaKernel.pFlat p}) (g.derivative.eval x₀)) := by
    rw [hg']
    simp
  obtain ⟨b, hb, hb₀⟩ := HenselianRing.is_henselian (I := Ideal.span {ThetaKernel.pFlat p}) g hm x₀ hroot hu
  refine ⟨b, ?_, ?_⟩
  · refine ⟨Polynomial.X ^ (p ^ d) - Polynomial.X, ?_, ?_⟩
    · apply Polynomial.monic_X_pow_sub
      rw [Polynomial.degree_X]
      exact WithBot.coe_lt_coe.mpr (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X]
      change g.eval b = 0 at hb
      simpa only [g, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] using hb
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb₀
    have he := congrArg (PrimitiveElements.tiltResidue p) hc
    rw [map_sub, map_mul, tiltResidue_pFlat, zero_mul, hx₀, sub_eq_zero] at he
    exact he

variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

theorem exists_coefficient_lift (a : k) :
    ∃ b : PreTilt 𝓞_ℂ_[p] p, IsIntegral (ZMod p) b ∧ PrimitiveElements.tiltResidue p b = j a := by
  obtain ⟨d, _, hd⟩ := FiniteField.card k p
  apply exists_finite_residue_lift p (j a) d d.pos
  rw [← hd, ← map_pow, FiniteField.pow_card]

def coefficientLift (a : k) : PreTilt 𝓞_ℂ_[p] p := (exists_coefficient_lift p j a).choose

theorem coefficientLift_integral (a : k) : IsIntegral (ZMod p) (coefficientLift p j a) :=
  (exists_coefficient_lift p j a).choose_spec.1

theorem coefficientLift_residue (a : k) : PrimitiveElements.tiltResidue p (coefficientLift p j a) = j a :=
  (exists_coefficient_lift p j a).choose_spec.2

/-- The uniquely determined coefficient field in the actual tilt. -/
def coefficientEmbedding : k →+* PreTilt 𝓞_ℂ_[p] p where
  toFun := coefficientLift p j
  map_zero' := integral_tilt_residue_injective p (coefficientLift_integral p j 0) isIntegral_zero (by
    rw [coefficientLift_residue, map_zero, map_zero])
  map_one' := integral_tilt_residue_injective p (coefficientLift_integral p j 1) isIntegral_one (by
    rw [coefficientLift_residue, map_one, map_one])
  map_add' a b := integral_tilt_residue_injective p (coefficientLift_integral p j (a + b))
    ((coefficientLift_integral p j a).add (coefficientLift_integral p j b)) (by
      rw [coefficientLift_residue, map_add, map_add, coefficientLift_residue, coefficientLift_residue])
  map_mul' a b := integral_tilt_residue_injective p (coefficientLift_integral p j (a * b))
    ((coefficientLift_integral p j a).mul (coefficientLift_integral p j b)) (by
      rw [coefficientLift_residue, map_mul, map_mul, coefficientLift_residue, coefficientLift_residue])

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients
