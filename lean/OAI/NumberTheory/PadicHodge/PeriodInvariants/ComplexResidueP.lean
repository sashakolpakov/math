import OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

/-! # Complex Residue P -/

namespace OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexResidueP

noncomputable section

/-!
# The residue map from O_Cp/p has nil kernel

Every element of the maximal ideal of O_Cp has norm below one, so some power
is divisible by p. Thus the kernel of O_Cp/p to the residue field consists of
nilpotent elements. This is the input for canonical finite-field lifting.
-/

open OAI.NumberTheory.PadicHodge.PeriodInvariants.PeriodRing

variable (p : ℕ) [Fact p.Prime]

abbrev ComplexResidue := IsLocalRing.ResidueField 𝓞_ℂ_[p]

instance integerEquiv_local (e : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p]) : IsLocalHom e.toRingHom :=
  isLocalHom_of_leftInverse e.symm.toRingHom e.symm_apply_apply

theorem p_mem_maximalIdeal : (p : 𝓞_ℂ_[p]) ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p] := by
  apply (Valuation.mem_maximalIdeal_iff ℂ_[p] (PadicComplex.valued p).v).mpr
  change Valued.v (p : ℂ_[p]) < 1
  rw [PadicComplex.valuation_p, one_div]
  exact inv_lt_one_of_one_lt₀ (show (1 : NNReal) < (p : NNReal) by
    exact_mod_cast (Fact.out : p.Prime).one_lt)

instance complexResidue_charP : CharP (ComplexResidue p) p := by
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast (IsLocalRing.residue 𝓞_ℂ_[p])]
  exact (IsLocalRing.residue_eq_zero_iff _).mpr (p_mem_maximalIdeal p)

def modPResidue : ModP 𝓞_ℂ_[p] p →+* ComplexResidue p :=
  Ideal.Quotient.lift (Ideal.span {(p : 𝓞_ℂ_[p])}) (IsLocalRing.residue 𝓞_ℂ_[p]) (by
    change Ideal.span {(p : 𝓞_ℂ_[p])} ≤ RingHom.ker (IsLocalRing.residue 𝓞_ℂ_[p])
    apply Ideal.span_le.mpr
    intro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact (IsLocalRing.residue_eq_zero_iff _).mpr (p_mem_maximalIdeal p))

theorem modPResidue_mk (x : 𝓞_ℂ_[p]) :
    modPResidue p (Ideal.Quotient.mk _ x) = IsLocalRing.residue 𝓞_ℂ_[p] x := rfl

theorem modPResidue_surjective : Function.Surjective (modPResidue p) := by
  intro x
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective x
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

theorem modPResidue_nil_kernel (x : ModP 𝓞_ℂ_[p] p) (hx : modPResidue p x = 0) : IsNilpotent x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ IsLocalRing.maximalIdeal 𝓞_ℂ_[p] := (IsLocalRing.residue_eq_zero_iff _).mp hx
  have hn : ‖a‖ < 1 := by
    have hv := (Valuation.mem_maximalIdeal_iff ℂ_[p] (PadicComplex.valued p).v).mp ha
    rw [← NNReal.coe_lt_coe, PeriodRing.complex_valuation_norm] at hv
    exact hv
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (PeriodRing.complexInt_norm_p_pos p) hn
  have hp : a ^ n ∈ (Ideal.span {(p : 𝓞_ℂ_[p])}) := by
    rw [← SetLike.mem_coe, PeriodRing.complexInt_span_closedBall, Metric.mem_closedBall, dist_zero_right, norm_pow]
    exact hn.le
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

end

end OAI.NumberTheory.PadicHodge.PeriodInvariants.ComplexResidueP
