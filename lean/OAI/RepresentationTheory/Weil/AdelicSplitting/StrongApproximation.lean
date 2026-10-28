import OAI.RepresentationTheory.Weil.AdelicSplitting.FiniteApproximation
import OAI.RepresentationTheory.Weil.AdelicSplitting.IntegralAdeles

/-! # Strong Approximation -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction

noncomputable section

/-! Strong approximation away from the archimedean places: the number field
is dense in its finite adeles. All completions and embeddings are the actual
ones used by the AdelicSplitting adelic oscillator. -/

open scoped _root_.NumberField Classical
open IsDedekindDomain

variable (F : Type) [Field F] [NumberField F]

theorem denseRange_integer_finiteIntegerProduct :
    DenseRange (fun a : 𝓞 F => fun v : HeightOneSpectrum (𝓞 F) =>
      algebraMap (𝓞 F) (v.adicCompletionIntegers F) a) := by
  intro x
  rw [mem_closure_iff]
  intro U hU hx
  obtain ⟨s, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  have hprecision : ∀ v : HeightOneSpectrum (𝓞 F), ∃ k : ℕ, v ∈ s →
      ∀ z : v.adicCompletionIntegers F,
        ‖z.val - (x v).val‖ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) → z ∈ u v := by
    intro v
    by_cases hv : v ∈ s
    · obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hu v hv).1 (x v) (hu v hv).2
      have hn : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
        exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
      obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hn)
      have hk' : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(k : ℤ)) < ε := by
        simpa only [zpow_neg, zpow_natCast, inv_pow] using hk
      refine ⟨k, fun _ z hz => hball ?_⟩
      rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
      exact hz.trans_lt hk'
    · exact ⟨0, fun h => (hv h).elim⟩
  choose k hk using hprecision
  obtain ⟨a, ha⟩ := FiniteApproximation.Construction.finite_integral_approximation F s x k
  refine ⟨(fun v => algebraMap (𝓞 F) (v.adicCompletionIntegers F) a),
    hsub ?_, Set.mem_range_self a⟩
  intro v hv
  exact hk v hv _ (ha v hv)

theorem denseRange_integer_finiteIntegralRing : DenseRange (IntegralAdeles.Construction.integerToFiniteIntegral F) := by
  have h := (IntegralAdeles.Construction.finiteIntegralProductHomeomorph F).surjective.denseRange.comp
    (denseRange_integer_finiteIntegerProduct F) (IntegralAdeles.Construction.finiteIntegralProductHomeomorph F).continuous
  simpa only [Function.comp_def, ← IntegralAdeles.Construction.integerToFiniteIntegral_eq_product] using h

theorem denseRange_rational_finiteAdeles : DenseRange (algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F)) := by
  let S := (algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F)).range
  have hO : ∀ a : IntegralAdeles.Construction.finiteIntegralRing F, a.val ∈ S.topologicalClosure := by
    intro a
    refine (denseRange_integer_finiteIntegralRing F).induction_on
      (p := fun a : IntegralAdeles.Construction.finiteIntegralRing F => a.val ∈ S.topologicalClosure) a
      (S.isClosed_topologicalClosure.preimage continuous_subtype_val) ?_
    intro r
    apply S.le_topologicalClosure
    exact ⟨algebraMap (𝓞 F) F r, (IsScalarTower.algebraMap_apply (𝓞 F) F (ArchimedeanAdeles.Construction.FiniteAdeles F) r).symm⟩
  intro a
  change a ∈ S.topologicalClosure
  obtain ⟨r, hr, hra⟩ := IntegralAdeles.Construction.exists_integer_multiple_finiteIntegral F a
  have hrF : algebraMap (𝓞 F) F r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hr
  have hid : algebraMap F (ArchimedeanAdeles.Construction.FiniteAdeles F) ((algebraMap (𝓞 F) F r)⁻¹) *
      algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r = 1 := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (ArchimedeanAdeles.Construction.FiniteAdeles F), ← map_mul, inv_mul_cancel₀ hrF, map_one]
  have hh := S.topologicalClosure.mul_mem
    (S.le_topologicalClosure (Set.mem_range_self ((algebraMap (𝓞 F) F r)⁻¹)))
    (hO ⟨algebraMap (𝓞 F) (ArchimedeanAdeles.Construction.FiniteAdeles F) r * a, hra⟩)
  simpa only [← mul_assoc, hid, one_mul] using hh

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.StrongApproximation.Construction
