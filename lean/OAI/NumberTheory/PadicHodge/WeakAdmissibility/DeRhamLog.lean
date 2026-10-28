import OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison

/-! # De Rham Log -/

namespace OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamLog

noncomputable section

/-! The completed crystalline logarithm maps to a nonzero de Rham logarithm. -/

open OAI.NumberTheory.PadicHodge.WeakAdmissibility.Logarithm.PeriodRings OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRham OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEmbedding OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamEnvelope
open OAI.NumberTheory.PadicHodge.WeakAdmissibility.FiniteDeRhamP OAI.NumberTheory.PadicHodge.WeakAdmissibility.Comparison OAI.NumberTheory.PadicHodge.WeakAdmissibility.BoundedCompletion
variable (p : ℕ) [Fact p.Prime]

def logCoefficient (n : ℕ) : Logarithm.PeriodRings.BInf p :=
  PeriodInvariants.Nontriviality.padicToBinf p ((-1 : ℚ_[p]) ^ n / (n + 1 : ℚ_[p]))

theorem logCoefficient_zero : logCoefficient p 0 = 1 := by simp [logCoefficient]

theorem logCoefficient_fraction (n : ℕ) :
    PeriodInvariants.Nontriviality.binfToFraction p (logCoefficient p n) =
      (-1 : Logarithm.PeriodRings.AInfFractionField p) ^ n / (n + 1 : Logarithm.PeriodRings.AInfFractionField p) := by
  change ((PeriodInvariants.Nontriviality.binfToFraction p).comp (PeriodInvariants.Nontriviality.padicToBinf p))
    ((-1 : ℚ_[p]) ^ n / (n + 1 : ℚ_[p])) = _
  rw [map_div₀, map_pow, map_neg, map_one, map_add, map_natCast, map_one]

theorem logTerm_bInf (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.thetaModP p x = 0) (n : ℕ) :
    DeRhamEnvelope.uncompletedToBInf p (Logarithm.PeriodRings.crystallineLogTerm p x hx n) =
      logCoefficient p n * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ (n + 1) := by
  apply PeriodInvariants.Nontriviality.binfToFraction_injective p
  rw [DeRhamEnvelope.uncompletedToBInf_fraction, Logarithm.PeriodRings.crystallineLogTerm_coe, map_mul, map_pow,
    logCoefficient_fraction, PeriodInvariants.Nontriviality.binfToFraction_algebraMap]
  ring

theorem aInf_kernel_bInf (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) :
    algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ∈ DeRham.deRhamIdeal p := by
  rw [RingHom.mem_ker, DeRham.bInfTheta_algebraMap, hx, map_zero]

def logFactorCauchy (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) :
    AdicCompletion.AdicCauchySequence (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p) :=
  AdicCompletion.AdicCauchySequence.mk (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p)
    (fun m => ∑ n ∈ Finset.range m,
      logCoefficient p n * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ n) (by
        intro m
        rw [SModEq.sub_mem, Finset.sum_range_succ]
        have hm := (DeRham.deRhamIdeal p ^ m).mul_mem_left (logCoefficient p m)
          (Ideal.pow_mem_pow (aInf_kernel_bInf p x hx) m)
        have he : (∑ n ∈ Finset.range m, logCoefficient p n * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ n) -
            ((∑ n ∈ Finset.range m, logCoefficient p n * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ n) +
              logCoefficient p m * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ m) =
            -(logCoefficient p m * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ m) := by ring
        rw [he]
        simpa only [smul_eq_mul, Ideal.mul_top] using (DeRham.deRhamIdeal p ^ m).neg_mem hm)

def logFactor (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) : Logarithm.PeriodRings.BdRPlus p :=
  AdicCompletion.mk (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p) (logFactorCauchy p x hx)

theorem logFactor_eval (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) (m : ℕ) :
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (logFactor p x hx) =
      Ideal.Quotient.mk _ (∑ n ∈ Finset.range m,
        logCoefficient p n * algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x ^ n) := by
  rw [logFactor, AdicCompletion.evalₐ_mk]
  rfl

theorem logFactor_isUnit (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0) : IsUnit (logFactor p x hx) := by
  let I := DeRham.deRhamIdeal p
  let y : AdicCompletion I (Logarithm.PeriodRings.BInf p) := logFactor p x hx
  change IsUnit y
  let J : Ideal (AdicCompletion I (Logarithm.PeriodRings.BInf p)) := I.map (algebraMap (Logarithm.PeriodRings.BInf p) (AdicCompletion I (Logarithm.PeriodRings.BInf p)))
  let : IsAdicComplete I (AdicCompletion I (Logarithm.PeriodRings.BInf p)) := AdicCompletion.isAdicComplete (DeRhamEmbedding.deRhamIdeal_fg p)
  let : IsAdicComplete J (AdicCompletion I (Logarithm.PeriodRings.BInf p)) :=
    (IsAdicComplete.map_algebraMap_iff I (AdicCompletion I (Logarithm.PeriodRings.BInf p))).mpr inferInstance
  apply Ideal.isUnit_of_sub_one_mem_jacobson_bot
  apply IsAdicComplete.le_jacobson_bot (I := J)
  change y - 1 ∈ I.map (algebraMap (Logarithm.PeriodRings.BInf p) (AdicCompletion I (Logarithm.PeriodRings.BInf p)))
  erw [← AdicCompletion.ker_evalOneₐ_eq_map (I := I) (DeRhamEmbedding.deRhamIdeal_fg p), RingHom.mem_ker,
    map_sub, map_one, sub_eq_zero]
  change AdicCompletion.evalOneₐ I y = 1
  rw [← AdicCompletion.factorₐ_evalₐ_one]
  change Ideal.Quotient.factor _ (AdicCompletion.evalₐ (DeRham.deRhamIdeal p) 1 (logFactor p x hx)) = 1
  rw [logFactor_eval]
  simp [logCoefficient_zero]

theorem logTerm_finite_zero (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0)
    (hxmod : Logarithm.PeriodRings.thetaModP p x = 0) (m n : ℕ) (hmn : m ≤ n + 1) :
    FiniteDeRhamP.uncompletedToFinite p m (Logarithm.PeriodRings.crystallineLogTerm p x hxmod n) = 0 := by
  change Ideal.Quotient.mk _ (DeRhamEnvelope.uncompletedToBInf p (Logarithm.PeriodRings.crystallineLogTerm p x hxmod n)) = 0
  rw [logTerm_bInf]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (DeRham.deRhamIdeal p ^ m).mul_mem_left _
    (Ideal.pow_le_pow_right hmn (Ideal.pow_mem_pow (aInf_kernel_bInf p x hx) (n + 1)))

theorem aCrisToFinite_log (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0)
    (hxmod : Logarithm.PeriodRings.thetaModP p x = 0) (m : ℕ) :
    Comparison.aCrisToFinite p m (Logarithm.PeriodRings.crystallineLog p x hxmod) =
      ∑ n ∈ Finset.range m, FiniteDeRhamP.uncompletedToFinite p m (Logarithm.PeriodRings.crystallineLogTerm p x hxmod n) := by
  apply BoundedCompletion.boundedExtension_mk_of_stable p m _ _ _ _ _ (Logarithm.PeriodRings.crystallineLogCauchy p x hxmod) _ m
  intro k hk
  change FiniteDeRhamP.uncompletedToFinite p m
    (∑ n ∈ Finset.range (p * k), Logarithm.PeriodRings.crystallineLogTerm p x hxmod n) = _
  rw [map_sum]
  symm
  apply Finset.sum_subset
  · apply Finset.range_mono
    exact hk.trans (Nat.le_mul_of_pos_left k (Fact.out : p.Prime).pos)
  · intro n _ hn
    exact logTerm_finite_zero p x hx hxmod m n
      (Nat.le_succ_of_le (Nat.le_of_not_lt (fun h => hn (Finset.mem_range.mpr h))))

theorem aCrisToBdRPlus_log (x : Logarithm.PeriodRings.AInf p) (hx : Logarithm.PeriodRings.theta p x = 0)
    (hxmod : Logarithm.PeriodRings.thetaModP p x = 0) :
    Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.crystallineLog p x hxmod) =
      DeRhamEmbedding.aInfToBdRPlus p x * logFactor p x hx := by
  apply AdicCompletion.ext_evalₐ
  intro m
  change AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.crystallineLog p x hxmod)) =
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m (DeRhamEmbedding.aInfToBdRPlus p x * logFactor p x hx)
  rw [Comparison.aCrisToBdRPlus_eval, aCrisToFinite_log p x hx hxmod]
  erw [map_mul, logFactor_eval]
  change (∑ n ∈ Finset.range m,
    Ideal.Quotient.mk _ (DeRhamEnvelope.uncompletedToBInf p (Logarithm.PeriodRings.crystallineLogTerm p x hxmod n))) =
    AdicCompletion.evalₐ (DeRham.deRhamIdeal p) m
      (AdicCompletion.of (DeRham.deRhamIdeal p) (Logarithm.PeriodRings.BInf p) (algebraMap (Logarithm.PeriodRings.AInf p) (Logarithm.PeriodRings.BInf p) x)) * _
  rw [AdicCompletion.evalₐ_of, ← map_mul, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [logTerm_bInf]
  apply congrArg (Ideal.Quotient.mk _)
  rw [pow_succ]
  ring

theorem cyclotomicPeriod_deRham_ne_zero :
    Comparison.aCrisToBdRPlus p (Logarithm.PeriodRings.cyclotomicPeriod p) ≠ 0 := by
  rw [Logarithm.PeriodRings.cyclotomicPeriod, aCrisToBdRPlus_log p (Logarithm.PeriodRings.cyclotomicDifference p)
    (Logarithm.PeriodRings.cyclotomicDifference_theta p) (Logarithm.PeriodRings.cyclotomicDifference_thetaModP p)]
  intro h
  have he : DeRhamEmbedding.aInfToBdRPlus p (Logarithm.PeriodRings.cyclotomicDifference p) = 0 :=
    (logFactor_isUnit p _ (Logarithm.PeriodRings.cyclotomicDifference_theta p)).mul_right_cancel
      (h.trans (zero_mul _).symm)
  exact DeRhamEmbedding.cyclotomicDifference_deRham_ne_zero p he

theorem cyclotomicPeriod_ne_zero : Logarithm.PeriodRings.cyclotomicPeriod p ≠ 0 := by
  intro h
  apply cyclotomicPeriod_deRham_ne_zero p
  rw [h, map_zero]

theorem cyclotomicPeriod_positive_ne_zero :
    algebraMap (Logarithm.PeriodRings.ACris p) (Logarithm.PeriodRings.BCrisPlus p) (Logarithm.PeriodRings.cyclotomicPeriod p) ≠ 0 := by
  intro h
  apply cyclotomicPeriod_deRham_ne_zero p
  rw [← Comparison.bCrisPlusToBdRPlus_algebraMap, h, map_zero]

end

end OAI.NumberTheory.PadicHodge.WeakAdmissibility.DeRhamLog
