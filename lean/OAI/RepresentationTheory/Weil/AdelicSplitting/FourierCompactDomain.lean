import OAI.RepresentationTheory.Weil.AdelicSplitting.CompactCharacter

/-! # Fourier Compact Domain -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FourierCompactDomain.LocalAnalysis

noncomputable section

section

/-! Fourier inversion on a compact frequency domain. Orthogonality gives
the precise scalar as the product of the volumes of a subgroup and its
annihilator. No inversion or Plancherel identity is assumed. -/

open _root_.MeasureTheory
open scoped Classical

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]

include hu hc in
theorem integral_localFourier_mul_swap {f g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ}
    (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x * g x ∂μ) =
      ∫ x, f x * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g x ∂μ := by
  have hL : (dotProductBilin k k : Local.FunctionsMetaplectic.Construction.Position k n →ₗ[k] Local.FunctionsMetaplectic.Construction.Position k n →ₗ[k] k).flip =
      dotProductBilin k k := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact FourierTools.LocalAnalysis.dot_comm y x
  have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
    (ContinuousLinearMap.mul ℂ ℂ) (L := dotProductBilin k k)
    (FourierTools.LocalAnalysis.circleCharacter_continuous ψ hu hc) (FourierTools.LocalAnalysis.dotProductBilin_continuous n) hf hg
  rw [hL, ← FourierTools.LocalAnalysis.fourierIntegral_eq_vectorFourier ψ hu,
    ← FourierTools.LocalAnalysis.fourierIntegral_eq_vectorFourier ψ hu] at h
  exact h

omit [LocallyCompactSpace k] in
theorem fourier_modulated_subgroup
    (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (x y : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator
      (fun ξ => ψ (-Local.FunctionsMetaplectic.Construction.dot x ξ))) y =
      if x + y ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup
        then (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0 := by
  rw [← CompactCharacter.LocalAnalysis.fourier_indicator_subgroup ψ μ U (x + y)]
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    by_cases hξ : ξ ∈ U
    · simp only [Set.indicator_of_mem hξ, one_mul]
      rw [← ψ.map_add_eq_mul]
      congr 1
      simp [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_comm]
    · simp [hξ]

include hu hc in
theorem fourier_square_compact_domain
    (U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)))
    (hAnn : IsOpen (CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)))
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ)
    (hF : tsupport (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U)
    (hTranslation : ∀ t ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup, ∀ y, f (y + t) = f y)
    (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x =
      ((μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) *
        μ.real (CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℝ) : ℂ) * f (-x) := by
  let g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ := (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun ξ => ψ (-Local.FunctionsMetaplectic.Construction.dot x ξ))
  have hg : Integrable g μ := by
    apply (integrable_indicator_iff U.isOpen.measurableSet).mpr
    apply ContinuousOn.integrableOn_compact hU
    apply Continuous.continuousOn
    apply hc.comp
    unfold Local.FunctionsMetaplectic.Construction.dot
    fun_prop
  have hcut : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x =
      ∫ ξ, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f ξ * g ξ ∂μ := by
    unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun ξ => by
      by_cases hξ : ξ ∈ U
      · simp [g, hξ]
      · have hz : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f ξ = 0 := by
          by_contra hn
          exact hξ (hF (subset_tsupport _ hn))
        change Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f ξ * _ = Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f ξ * _
        rw [hz, zero_mul, zero_mul]
  rw [hcut, integral_localFourier_mul_swap ψ hu hc μ hf hg]
  have hshift := integral_add_right_eq_self (μ := μ)
    (fun y => f y * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g y) (-x)
  rw [← hshift]
  have he : (fun y => f (y + -x) * Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g (y + -x)) =
      (CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator
        (fun _ => f (-x) * (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ)) := by
    funext y
    rw [show Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g (y + -x) =
      if x + (y + -x) ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup
        then (μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0 from
      fourier_modulated_subgroup ψ μ U x (y + -x)]
    rw [show x + (y + -x) = y by abel]
    by_cases hy : y ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup
    · rw [ite_eq_left hy, Set.indicator_of_mem hy]
      rw [add_comm y (-x), hTranslation y hy (-x)]
    · simp [hy]
  rw [he, integral_indicator_const _ hAnn.measurableSet]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  ring

end

/-! Compact frequency domains adapted to nonarchimedean test functions. -/

open _root_.MeasureTheory
open scoped Classical

theorem additiveAnnihilator_small
    {k : Type} [NormedField k] {n : ℕ}
    (ψ : AddChar k ℂ) (a : k) (ha : ψ a ≠ 1)
    (U : AddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)) (ε R : ℝ) (hε : 0 < ε)
    (hR : ‖a‖ / ε ≤ R)
    (hU : Metric.closedBall (0 : Local.FunctionsMetaplectic.Construction.Position k n) R ⊆ U) :
    ∀ x ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U, ‖x‖ < ε := by
  intro x hx
  apply (pi_norm_lt_iff hε).mpr
  intro i
  by_contra! hi
  have hxi : x i ≠ 0 := norm_pos_iff.mp (hε.trans_le hi)
  let t : Local.FunctionsMetaplectic.Construction.Position k n := Pi.single i (a / x i)
  have ht : t ∈ U := by
    apply hU
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(Pi.single i (a / x i) : Local.FunctionsMetaplectic.Construction.Position k n)‖ ≤ R
    rw [Pi.norm_single, norm_div]
    exact (div_le_div_of_nonneg_left (norm_nonneg _) hε hi).trans hR
  have hdot : Local.FunctionsMetaplectic.Construction.dot x t = a := by
    simp only [Local.FunctionsMetaplectic.Construction.dot, t, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true]
    field_simp
  apply ha
  have h := hx t ht
  rwa [hdot] at h

theorem exists_adapted_frequency_subgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    [ProperSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : IsLocallyConstant f) (hs : HasCompactSupport f) :
    ∃ U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n), IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) ∧
      tsupport (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U ∧
      ∀ t ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, f (x + t) = f x := by
  have hF := NonarchimedeanIntertwiner.LocalAnalysis.fourierIntegral_compactSupport_of_locallyConstant ψ hn μ hf hs
  obtain ⟨R, hR, hbound⟩ := hF.isBounded.exists_pos_norm_le
  obtain ⟨ε, hε, heq⟩ := NonarchimedeanIntertwiner.LocalAnalysis.compact_locallyConstant_translation hf hs
  obtain ⟨a, ha⟩ := hn
  let S : ℝ := max R (‖a‖ / ε) + 1
  have hS : 0 < S := by
    exact lt_trans hR (lt_add_of_le_of_pos (le_max_left _ _) zero_lt_one)
  let U := IsUltrametricDist.closedBall_openAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n) hS
  have hUS : (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) = Metric.closedBall 0 S := rfl
  refine ⟨U, ?_, ?_, ?_⟩
  · rw [hUS]
    exact isCompact_closedBall _ _
  · intro x hx
    rw [hUS, Metric.mem_closedBall, dist_zero_right]
    exact (hbound x hx).trans ((le_max_left _ _).trans (le_add_of_nonneg_right zero_le_one))
  · intro t ht x
    apply heq x t
    apply additiveAnnihilator_small ψ a ha U.toAddSubgroup ε S hε _ _ t ht
    · exact (le_max_right _ _).trans (le_add_of_nonneg_right zero_le_one)
    · exact fun _ hx => hx

theorem openAddSubgroup_sup_compact
    {E : Type*} [TopologicalSpace E] [AddCommGroup E] [IsTopologicalAddGroup E]
    (U V : OpenAddSubgroup E) (hU : IsCompact (U : Set E)) (hV : IsCompact (V : Set E)) :
    IsCompact ((U ⊔ V : OpenAddSubgroup E) : Set E) := by
  have he : ((U ⊔ V : OpenAddSubgroup E) : Set E) =
      (fun p : E × E => p.1 + p.2) '' ((U : Set E) ×ˢ (V : Set E)) := by
    ext x
    change x ∈ U.toAddSubgroup ⊔ V.toAddSubgroup ↔ _
    rw [AddSubgroup.mem_sup]
    constructor
    · rintro ⟨u, hu, v, hv, h⟩
      exact ⟨(u, v), ⟨hu, hv⟩, h⟩
    · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, h⟩
      exact ⟨u, hu, v, hv, h⟩
  rw [he]
  exact (hU.prod hV).image (continuous_fst.add continuous_snd)

theorem additiveAnnihilator_antitone
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    {U V : AddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n)} (hUV : U ≤ V) :
    CompactCharacter.LocalAnalysis.additiveAnnihilator ψ V ≤ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U := by
  intro x hx y hy
  exact hx y (hUV hy)

theorem exists_common_adapted_frequency_subgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k] [ProperSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f g : Local.FunctionsMetaplectic.Construction.Position k n → ℂ}
    (hf : IsLocallyConstant f) (hsf : HasCompactSupport f)
    (hg : IsLocallyConstant g) (hsg : HasCompactSupport g) :
    ∃ U : OpenAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n), IsCompact (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) ∧
      tsupport (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U ∧ tsupport (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ g) ⊆ U ∧
      (∀ t ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, f (x + t) = f x) ∧
      (∀ t ∈ CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, g (x + t) = g x) := by
  obtain ⟨U, hU, hUf, hUt⟩ := exists_adapted_frequency_subgroup ψ hn μ hf hsf
  obtain ⟨V, hV, hVg, hVt⟩ := exists_adapted_frequency_subgroup ψ hn μ hg hsg
  refine ⟨U ⊔ V, openAddSubgroup_sup_compact U V hU hV,
    fun x hx => (show U.toAddSubgroup ≤ (U ⊔ V).toAddSubgroup from le_sup_left) (hUf hx),
    fun x hx => (show V.toAddSubgroup ≤ (U ⊔ V).toAddSubgroup from le_sup_right) (hVg hx), ?_, ?_⟩
  · intro t ht x
    apply hUt t _ x
    exact additiveAnnihilator_antitone ψ
      (show U.toAddSubgroup ≤ (U ⊔ V).toAddSubgroup from le_sup_left) ht
  · intro t ht x
    apply hVt t _ x
    exact additiveAnnihilator_antitone ψ
      (show V.toAddSubgroup ≤ (U ⊔ V).toAddSubgroup from le_sup_right) ht

theorem measureReal_open_compact_pos
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {S : Set E} (hS : IsOpen S) (hC : IsCompact S) (hN : S.Nonempty) : 0 < μ.real S := by
  apply ENNReal.toReal_pos
  · exact (Measure.measure_pos_of_nonempty_interior μ (by rwa [hS.interior_eq])).ne'
  · exact hC.measure_ne_top

theorem nonarchimedean_fourier_square_scalar
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k] [ProperSpace k] [SecondCountableTopology k]
    [NonarchimedeanAddGroup k] (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ) (hn : ∃ t, ψ t ≠ 1)
    (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = (c : ℂ) * f.val (-x) := by
  let B := IsUltrametricDist.closedBall_openAddSubgroup (Local.FunctionsMetaplectic.Construction.Position k n) (by norm_num : (0 : ℝ) < 1)
  have hB : IsCompact (B : Set (Local.FunctionsMetaplectic.Construction.Position k n)) := isCompact_closedBall _ _
  let φ : Local.FunctionsMetaplectic.Construction.Position k n → ℂ := (B : Set (Local.FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1)
  have hφc : IsLocallyConstant φ := CompactCharacter.LocalAnalysis.subgroup_indicator_locallyConstant B
  have hφs : HasCompactSupport φ := CompactCharacter.LocalAnalysis.subgroup_indicator_compactSupport B hB
  have hφi : Integrable φ μ := hφc.continuous.integrable_of_hasCompactSupport hφs
  have hφ0 : φ 0 = 1 := Set.indicator_of_mem B.zero_mem _
  obtain ⟨U, hU, hFU, htU⟩ := exists_adapted_frequency_subgroup ψ hn μ hφc hφs
  have hAU := CompactCharacter.LocalAnalysis.additiveAnnihilator_compact_open ψ hu hc hn μ U hU
  let c : ℝ := μ.real (U : Set (Local.FunctionsMetaplectic.Construction.Position k n)) *
    μ.real (CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup : Set (Local.FunctionsMetaplectic.Construction.Position k n))
  have hcpos : 0 < c := mul_pos
    (measureReal_open_compact_pos μ U.isOpen hU ⟨0, U.zero_mem⟩)
    (measureReal_open_compact_pos μ hAU.2 hAU.1 ⟨0, (CompactCharacter.LocalAnalysis.additiveAnnihilator ψ U.toAddSubgroup).zero_mem⟩)
  have hcφ : Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ φ) 0 = (c : ℂ) := by
    have h := fourier_square_compact_domain ψ hu hc μ U hU hAU.2 hφi hFU htU 0
    simpa only [neg_zero, hφ0, mul_one] using h
  refine ⟨c, hcpos, ?_⟩
  intro f x
  obtain ⟨hfc, hfs⟩ := NonarchimedeanIntertwiner.LocalAnalysis.schwartzBruhat_totallyDisconnected_iff.mp f.property
  obtain ⟨V, hV, hFf, hFφ, htf, htφ⟩ :=
    exists_common_adapted_frequency_subgroup ψ hn μ hfc hfs hφc hφs
  have hAV := CompactCharacter.LocalAnalysis.additiveAnnihilator_compact_open ψ hu hc hn μ V hV
  have hcV := fourier_square_compact_domain ψ hu hc μ V hV hAV.2 hφi hFφ htφ 0
  rw [hcφ, neg_zero, hφ0, mul_one] at hcV
  have h := fourier_square_compact_domain ψ hu hc μ V hV hAV.2
    (TestSpace.LocalAnalysis.schwartzBruhat_integrable μ f) hFf htf x
  rw [← hcV] at h
  exact h

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FourierCompactDomain.LocalAnalysis
