import OAI.RepresentationTheory.Weil.AdelicSplitting.LocalCompact

/-! # Finite Approximation -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteApproximation.Construction

noncomputable section

/-! Simultaneous approximation in the actual finite integer completions of
an arbitrary number field, using powers of distinct prime ideals and CRT. -/

open scoped _root_.NumberField Classical NNReal
open IsDedekindDomain

variable (F : Type*) [Field F] [NumberField F]

private theorem norm_lt_prime_precision (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) (k : ℕ) :
    ‖x‖ < (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) ↔
      Valued.v x < WithZero.exp (-(k : ℤ)) := by
  rw [NumberField.FinitePlace.norm_def]
  have he : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (WithZero.exp (-(k : ℤ))) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(k : ℤ)) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have heR := congrArg (fun t : ℝ≥0 => (t : ℝ)) he
  simp only [NNReal.coe_zpow, NNReal.coe_natCast] at heR
  rw [← heR, NNReal.coe_lt_coe]
  exact (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).lt_iff_lt

private theorem norm_le_prime_precision (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletion F) (k : ℕ) :
    ‖x‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) ↔
      Valued.v x ≤ WithZero.exp (-(k : ℤ)) := by
  rw [NumberField.FinitePlace.norm_def]
  have he : WithZeroMulInt.toNNReal (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
      (WithZero.exp (-(k : ℤ))) = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (-(k : ℤ)) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
    rfl
  have heR := congrArg (fun t : ℝ≥0 => (t : ℝ)) he
  simp only [NNReal.coe_zpow, NNReal.coe_natCast] at heR
  rw [← heR, NNReal.coe_le_coe]
  exact (WithZeroMulInt.toNNReal_strictMono
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v)).le_iff_le

theorem integral_prime_power_approximation (v : HeightOneSpectrum (𝓞 F))
    (x : v.adicCompletionIntegers F) (k : ℕ) :
    ∃ a : 𝓞 F, ‖algebraMap (𝓞 F) (v.adicCompletion F) a - x.val‖ <
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) := by
  let ε : ℝ := (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ))
  have hn : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).trans' Nat.zero_lt_one
  have hε : 0 < ε := zpow_pos hn _
  obtain ⟨q, hq⟩ := (HeightOneSpectrum.denseRange_algebraMap (K := F) v).exists_dist_lt
    x.val (lt_min hε zero_lt_one)
  rw [dist_eq_norm, norm_sub_rev] at hq
  have hx : ‖x.val‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.mpr x.property
  have hqint : ‖algebraMap F (v.adicCompletion F) q‖ ≤ 1 := by
    calc
      _ = ‖(algebraMap F (v.adicCompletion F) q - x.val) + x.val‖ := by rw [sub_add_cancel]
      _ ≤ max ‖algebraMap F (v.adicCompletion F) q - x.val‖ ‖x.val‖ :=
        Valuation.norm_add_le Valued.v _ _
      _ ≤ 1 := max_le (hq.trans_le (min_le_right _ _)).le hx
  have hqval : v.valuation F q ≤ 1 := by
    have h := Valued.toNormedField.norm_le_one_iff.mp hqint
    change Valued.v (q : v.adicCompletion F) ≤ 1 at h
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hqval
    (Units.mk0 (WithZero.exp (-(k : ℤ))) (WithZero.exp_ne_zero))
  have haq : ‖algebraMap (𝓞 F) (v.adicCompletion F) a -
      algebraMap F (v.adicCompletion F) q‖ < ε := by
    apply (norm_lt_prime_precision F v _ k).mpr
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub]
    change Valued.v ((algebraMap (𝓞 F) F a - q : F) : v.adicCompletion F) < _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  refine ⟨a, ?_⟩
  calc
    _ = ‖(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q) +
          (algebraMap F (v.adicCompletion F) q - x.val)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) q‖
          ‖algebraMap F (v.adicCompletion F) q - x.val‖ := Valuation.norm_add_le Valued.v _ _
    _ < ε := max_lt haq (hq.trans_le (min_le_left _ _))

theorem finite_integral_approximation
    (s : Finset (HeightOneSpectrum (𝓞 F)))
    (x : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (k : HeightOneSpectrum (𝓞 F) → ℕ) :
    ∃ a : 𝓞 F, ∀ v ∈ s,
      ‖algebraMap (𝓞 F) (v.adicCompletion F) a - (x v).val‖ ≤
        (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k v : ℤ)) := by
  choose b hb using (fun v => integral_prime_power_approximation F v (x v) (k v))
  let I : s → Ideal (𝓞 F) := fun v => v.val.asIdeal ^ k v.val
  have hI : Pairwise (Function.onFun IsCoprime I) := by
    intro v w hvw
    exact HeightOneSpectrum.isCoprime_pow_of_ne v.val w.val
      (fun h => hvw (Subtype.ext h)) _ _
  obtain ⟨a, ha⟩ := Ideal.exists_forall_sub_mem_ideal hI (fun v : s => b v.val)
  refine ⟨a, ?_⟩
  intro v hv
  have hab : ‖algebraMap (𝓞 F) (v.adicCompletion F) a -
      algebraMap (𝓞 F) (v.adicCompletion F) (b v)‖ ≤
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k v : ℤ)) := by
    apply (norm_le_prime_precision F v _ (k v)).mpr
    rw [← map_sub, IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
    change Valued.v ((algebraMap (𝓞 F) F (a - b v) : F) : v.adicCompletion F) ≤ _
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem v _ _).mpr (ha ⟨v, hv⟩)
  calc
    _ = ‖(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap (𝓞 F) (v.adicCompletion F) (b v)) +
          (algebraMap (𝓞 F) (v.adicCompletion F) (b v) - (x v).val)‖ := by rw [sub_add_sub_cancel]
    _ ≤ max ‖algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap (𝓞 F) (v.adicCompletion F) (b v)‖
          ‖algebraMap (𝓞 F) (v.adicCompletion F) (b v) - (x v).val‖ := Valuation.norm_add_le Valued.v _ _
    _ ≤ _ := max_le hab (hb v).le

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteApproximation.Construction
