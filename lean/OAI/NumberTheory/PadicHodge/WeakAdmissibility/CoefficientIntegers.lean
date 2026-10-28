import OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields
import OAI.NumberTheory.PadicHodge.WeakAdmissibility.WittUnramified

/-! # Coefficient Integers -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientIntegers

noncomputable section

/-! Integral coefficient embeddings and their actual p-adic norms. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.PrimitiveElements OAI.NumberTheory.PadicHodge.WeakAdmissibility.UnramifiedCoefficients OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientComparison
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.AlgebraicCoefficientFields OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamField.Constants OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamDVR OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.TiltCoefficients
variable (p : ℕ) [Fact p.Prime]
variable {k : Type*} [Field k] [Fintype k] [CharP k p] (j : k →+* PrimitiveElements.ResidueCp p)

def coefficientIntegerToCp : WittVector p k →+* 𝓞_ℂ_[p] := (Logarithm.PeriodRings.theta p).comp (UnramifiedCoefficients.coefficientToAInf p j)

theorem theta_residue (x : Logarithm.PeriodRings.AInf p) :
    IsLocalRing.residue 𝓞_ℂ_[p] (Logarithm.PeriodRings.theta p x) = PrimitiveElements.tiltResidue p (x.coeff 0) :=
  congrArg (PrimitiveElements.residueModP p) (Logarithm.PeriodRings.thetaModP_eq p x)

theorem coefficientIntegerToCp_residue (x : WittVector p k) :
    IsLocalRing.residue 𝓞_ℂ_[p] (coefficientIntegerToCp p j x) = j (x.coeff 0) := by
  change IsLocalRing.residue 𝓞_ℂ_[p] (Logarithm.PeriodRings.theta p (UnramifiedCoefficients.coefficientToAInf p j x)) = _
  rw [theta_residue]
  change PrimitiveElements.tiltResidue p ((WittVector.map (TiltCoefficients.coefficientEmbedding p j) x).coeff 0) = _
  rw [WittVector.map_coeff]
  exact TiltCoefficients.coefficientLift_residue p j (x.coeff 0)

theorem coefficientResidue_integer (x : WittVector p k) :
    AlgebraicCoefficientFields.coefficientResidueAlg p j (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x) =
      (coefficientIntegerToCp p j x : ℂ_[p]) := by
  change DeRhamDVR.residue p (CoefficientComparison.coefficientFieldToCompletion p j
    (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x)) = _
  rw [CoefficientComparison.coefficientFieldToCompletion_integer]
  change DeRhamDVR.residue p (algebraMap (Logarithm.PeriodRings.BInf p) (DeRhamDVR.DeRhamCompletion p)
    (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) (UnramifiedCoefficients.coefficientToAInf p j x))) = _
  rw [DeRhamDVR.residue_of, DeRham.bInfTheta_algebraMap, DeRham.integerLocalizationToCp_algebraMap]
  rfl

theorem coefficientIntegerToCp_unit_norm (u : (WittVector p k)ˣ) :
    ‖(coefficientIntegerToCp p j u : ℂ_[p])‖ = 1 := by
  have h := (Valuation.integer.integers (Valued.v : Valuation ℂ_[p] NNReal)).one_of_isUnit
    (u.isUnit.map (coefficientIntegerToCp p j))
  change Valued.v (coefficientIntegerToCp p j u : ℂ_[p]) = 1 at h
  rw [Logarithm.PeriodRings.valuation_eq_nnnorm] at h
  exact congrArg (fun r : NNReal => (r : ℝ)) h

theorem coefficientIntegerToCp_norm (n : ℕ) (u : (WittVector p k)ˣ) :
    ‖(coefficientIntegerToCp p j ((p : WittVector p k) ^ n * u) : ℂ_[p])‖ = ‖(p : ℂ_[p])‖ ^ n := by
  rw [map_mul, map_pow, map_natCast]
  change ‖(p : ℂ_[p]) ^ n * (coefficientIntegerToCp p j u : ℂ_[p])‖ = _
  rw [norm_mul, norm_pow, coefficientIntegerToCp_unit_norm, mul_one]

theorem coefficientAlgebraic_integer_norm (x : WittVector p k) :
    ‖AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j
      (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x)‖ =
        ‖(coefficientIntegerToCp p j x : ℂ_[p])‖ := by
  have he := AlgebraicCoefficientFields.coefficientFieldToAlgebraic_residue p j
    (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) x)
  rw [coefficientResidue_integer] at he
  exact (PadicComplex.norm_extends p _).symm.trans (congrArg norm he)

theorem coefficientAlgebraic_norm_le_iff (x : UnramifiedCoefficients.CoefficientField (p := p) (k := k)) :
    ‖AlgebraicCoefficientFields.coefficientFieldToAlgebraic p j x‖ ≤ 1 ↔
      ∃ a : WittVector p k, algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) a = x := by
  constructor
  · intro hx
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := WittVector p k) x
    have hb0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hb' : algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)) b ≠ 0 :=
      fun h => hb0 ((IsFractionRing.injective (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)))
        (h.trans (map_zero _).symm))
    by_cases ha0 : a = 0
    · refine ⟨0, ?_⟩
      simp only [ha0, map_zero, zero_div]
    obtain ⟨m, u, ha⟩ := WittVector.exists_eq_pow_p_mul' a ha0
    obtain ⟨n, v, hbform⟩ := WittVector.exists_eq_pow_p_mul' b hb0
    rw [map_div₀, norm_div, coefficientAlgebraic_integer_norm, coefficientAlgebraic_integer_norm,
      ha, hbform, coefficientIntegerToCp_norm, coefficientIntegerToCp_norm,
      div_le_one (pow_pos (Logarithm.PeriodRings.norm_p_pos p) n)] at hx
    have hnm : n ≤ m := (pow_le_pow_iff_right_of_lt_one₀ (Logarithm.PeriodRings.norm_p_pos p) (Logarithm.PeriodRings.norm_p_lt_one p)).mp hx
    refine ⟨(p : WittVector p k) ^ (m - n) * (↑u * ↑v⁻¹), (eq_div_iff hb').mpr ?_⟩
    rw [← map_mul, ha, hbform]
    apply congrArg (algebraMap (WittVector p k) (UnramifiedCoefficients.CoefficientField (p := p) (k := k)))
    calc
      (p : WittVector p k) ^ (m - n) * (↑u * ↑v⁻¹) * (p ^ n * ↑v) =
          (p ^ (m - n) * p ^ n) * ↑u * (↑v⁻¹ * ↑v) := by ring
      _ = p ^ m * ↑u := by rw [Units.inv_mul, mul_one, ← pow_add, Nat.sub_add_cancel hnm]
  · rintro ⟨a, rfl⟩
    rw [coefficientAlgebraic_integer_norm]
    exact (PeriodInvariants.PeriodRing.complex_mem_integer_iff_norm p _).mp (coefficientIntegerToCp p j a).property

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.CoefficientIntegers
