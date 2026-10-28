import OAI.RepresentationTheory.Weil.Local.SchurIndicators

/-! # Bruhat Cosets -/

namespace OAI.RepresentationTheory.Weil.Local.BruhatCosets.Construction

noncomputable section

section

/-! Exact finite coset expansions of compact locally constant functions. -/

open scoped Classical

theorem compact_locallyConstant_coset_expansion
    {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [ProperSpace E]
    {f : E → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ U : OpenAddSubgroup E, IsCompact (U : Set E) ∧
      ∃ s : Finset (E ⧸ U.toAddSubgroup), ∀ x,
        f x = ∑ c ∈ s, f c.out * (U : Set E).indicator (fun _ => (1 : ℂ)) (x - c.out) := by
  obtain ⟨ε, hε, hperiod⟩ := CompactCharacter.Construction.compact_locallyConstant_translation hf hs
  let U := IsUltrametricDist.closedBall_openAddSubgroup E (half_pos hε)
  let q : E → E ⧸ U.toAddSubgroup := QuotientAddGroup.mk
  have hp (x t : E) (ht : t ∈ U) : f (x + t) = f x := by
    apply hperiod x t
    exact (show ‖t‖ ≤ ε / 2 by
      change t ∈ Metric.closedBall 0 (ε / 2) at ht
      simpa only [Metric.mem_closedBall, dist_zero_right] using ht).trans_lt (half_lt_self hε)
  have hrep (x : E) : f (q x).out = f x := by
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_out_eq_add U.toAddSubgroup x
    change f (QuotientAddGroup.mk x : E ⧸ U.toAddSubgroup).out = f x
    rw [ht]
    exact hp x t.val t.property
  have hmem (x : E) (c : E ⧸ U.toAddSubgroup) : x - c.out ∈ U ↔ q x = c := by
    change x - c.out ∈ U.toAddSubgroup ↔ _
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq']
  have hfinite : (q '' tsupport f).Finite :=
    (hs.image (show Continuous q from QuotientAddGroup.continuous_mk)).finite_of_discrete
  let s := hfinite.toFinset
  refine ⟨U, isCompact_closedBall 0 (ε / 2), s, fun x => ?_⟩
  have hind (c : E ⧸ U.toAddSubgroup) :
      (U : Set E).indicator (fun _ => (1 : ℂ)) (x - c.out) = if q x = c then 1 else 0 := by
    by_cases hc : q x = c
    · simp [Set.indicator_of_mem ((hmem x c).mpr hc), hc]
    · simp [Set.indicator_of_notMem (fun h => hc ((hmem x c).mp h)), hc]
  simp only [hind, mul_ite, mul_one, mul_zero]
  by_cases hx : q x ∈ s
  · rw [Finset.sum_eq_single (q x)]
    · simp [hrep]
    · intro c _ hc
      simp only [ite_eq_right (Ne.symm hc)]
    · exact fun h => False.elim (h hx)
  · have hfx : f x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hx (hfinite.mem_toFinset.mpr ⟨x, h, rfl⟩)
    rw [hfx]
    symm
    apply Finset.sum_eq_zero
    intro c hc
    exact ite_eq_right (by intro h; apply hx; rw [h]; exact hc)

end

/-! Scalarity of the actual nonarchimedean oscillator kernel. -/

open _root_.MeasureTheory
open scoped Classical

theorem oscillator_kernel_every_vector_eigen
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) : ∃ c : ℂ, g.val.2 f = c • f := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  obtain ⟨U, hU, s, hsum⟩ := compact_locallyConstant_coset_expansion hf hs
  let b : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
      (CompactCharacter.Construction.subgroup_indicator_compactSupport U hU)⟩
  let c := (g.val.2 b).val 0
  have hb : g.val.2 b = c • b := by
    apply Subtype.ext
    funext x
    exact SchurIndicators.Construction.oscillator_kernel_indicator_eigenvector hNondiscrete ψ hu hc hn g hg U hU x
  let bt (t : FunctionsMetaplectic.Construction.Position k n) : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨fun x => b.val (x - t),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem
      ((CompactCharacter.Construction.subgroup_indicator_locallyConstant U).comp_continuous (continuous_id.sub continuous_const))
      ((CompactCharacter.Construction.subgroup_indicator_compactSupport U hU).comp_homeomorph (Homeomorph.subRight t))⟩
  have hbt (t : FunctionsMetaplectic.Construction.Position k n) : g.val.2 (bt t) = c • bt t := by
    have hh : (bt t).val = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim t 0) b.val := by
      have h := SchurIndicators.Construction.heisenberg_pure_translation ψ (-t) b.val
      simpa only [bt, neg_neg, sub_eq_add_neg] using! h.symm
    have h := SchurIndicators.Construction.oscillator_kernel_heisenberg ψ g hg (Sum.elim t 0) b (bt t) hh
    rw [hb] at h
    change (g.val.2 (bt t)).val = FunctionsMetaplectic.Construction.heisenbergFunction ψ (Sum.elim t 0) (c • b.val) at h
    rw [LinearIntertwiner.Construction.heisenbergFunction_smul, ← hh] at h
    exact Subtype.ext h
  have hdecomp : f = ∑ z ∈ s, f.val z.out • bt z.out := by
    apply Subtype.ext
    funext x
    simpa only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using hsum x
  refine ⟨c, ?_⟩
  calc
    _ = g.val.2 (∑ z ∈ s, f.val z.out • bt z.out) := congrArg g.val.2 hdecomp
    _ = ∑ z ∈ s, f.val z.out • g.val.2 (bt z.out) := by simp only [map_sum, map_smul]
    _ = ∑ z ∈ s, c • (f.val z.out • bt z.out) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hbt, smul_comm]
    _ = c • f := by rw [← Finset.smul_sum, ← hdecomp]

theorem function_submodule_scalar_of_every_vector_eigen
    {X : Type*} (S : Submodule ℂ (X → ℂ)) (T : S →ₗ[ℂ] S)
    (heigen : ∀ f : S, ∃ c : ℂ, T f = c • f)
    (x₀ : X) (b : S) (hb : b.val x₀ = 1) : ∃ c : ℂ, ∀ f : S, T f = c • f := by
  obtain ⟨c, hc⟩ := heigen b
  have hzero (f : S) (hf : f.val x₀ = 0) : T f = c • f := by
    obtain ⟨a, ha⟩ := heigen f
    obtain ⟨d, hd⟩ := heigen (f + b)
    have h : a • f + c • b = d • (f + b) := by rwa [map_add, ha, hc] at hd
    have heval := congrArg (fun z : S => z.val x₀) h
    change a * f.val x₀ + c * b.val x₀ = d * (f.val x₀ + b.val x₀) at heval
    have hdc : d = c := by simpa only [hf, hb, mul_zero, zero_add, mul_one] using heval.symm
    rw [hdc, smul_add] at h
    exact ha.trans (add_right_cancel h)
  refine ⟨c, fun f => ?_⟩
  let h := f - f.val x₀ • b
  have hh : h.val x₀ = 0 := by change f.val x₀ - f.val x₀ * b.val x₀ = 0; rw [hb]; ring
  have ht := hzero h hh
  change T (f - f.val x₀ • b) = c • (f - f.val x₀ • b) at ht
  rw [map_sub, map_smul, hc, smul_sub, smul_comm (f.val x₀) c b] at ht
  exact sub_left_inj.mp ht

theorem nonarchimedean_oscillator_kernel_scalar
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1) :
    ∃ c : ℂ, ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, g.val.2 f = c • f := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  let b : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
      (CompactCharacter.Construction.subgroup_indicator_compactSupport U (isCompact_closedBall 0 1))⟩
  exact function_submodule_scalar_of_every_vector_eigen (FunctionsMetaplectic.Construction.schwartzBruhat k n) g.val.2.toLinearMap
    (oscillator_kernel_every_vector_eigen hNondiscrete ψ hu hc hn g hg) 0 b (by simp [b])

theorem l2Energy_smul
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (c : ℂ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.l2Energy k n (c • f) = ‖c‖ ^ 2 * FunctionsMetaplectic.Construction.l2Energy k n f := by
  unfold FunctionsMetaplectic.Construction.l2Energy
  simp only [Submodule.coe_smul, Pi.smul_apply, norm_smul, mul_pow]
  rw [integral_const_mul]

theorem nonarchimedean_oscillator_kernel_unit_scalar
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g : FunctionsMetaplectic.Construction.Oscillator k n ψ) (hg : OscillatorProjection.Construction.oscillatorProjection k n ψ g = 1) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, g.val.2 f = c • f := by
  obtain ⟨c, hscalar⟩ := nonarchimedean_oscillator_kernel_scalar hNondiscrete ψ hu hc hn g hg
  refine ⟨c, ?_, hscalar⟩
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  let b : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
      (CompactCharacter.Construction.subgroup_indicator_compactSupport U (isCompact_closedBall 0 1))⟩
  have hb : b ≠ 0 := by
    intro h
    have hv := congrArg (fun f : FunctionsMetaplectic.Construction.schwartzBruhat k n => f.val 0) h
    simp [b] at hv
  have hE : FunctionsMetaplectic.Construction.l2Energy k n b ≠ 0 := fun h => hb ((FunctionsMetaplectic.Construction.l2Energy_eq_zero_iff k hNondiscrete n b).mp h)
  have h := g.property.1 b
  rw [hscalar, l2Energy_smul] at h
  have hs : ‖c‖ ^ 2 = 1 := mul_right_cancel₀ hE (h.trans (one_mul _).symm)
  nlinarith [norm_nonneg c]

theorem nonarchimedean_oscillator_equal_projection
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (g h : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hgh : OscillatorProjection.Construction.oscillatorProjection k n ψ g = OscillatorProjection.Construction.oscillatorProjection k n ψ h) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, h.val.2 f = c • g.val.2 f := by
  have hproj : OscillatorProjection.Construction.oscillatorProjection k n ψ (h * g⁻¹) = 1 := by rw [map_mul, map_inv, hgh, mul_inv_cancel]
  obtain ⟨c, hc, hs⟩ := nonarchimedean_oscillator_kernel_unit_scalar hNondiscrete ψ hu hc hn (h * g⁻¹) hproj
  refine ⟨c, hc, fun f => ?_⟩
  have heq := hs (g.val.2 f)
  change h.val.2 (g.val.2.symm (g.val.2 f)) = _ at heq
  simpa only [LinearEquiv.symm_apply_apply] using heq

end

end OAI.RepresentationTheory.Weil.Local.BruhatCosets.Construction
