import OAI.RepresentationTheory.Weil.Local.QuadraticFourier

/-! # Gaussian Compact -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianCompact.Construction

noncomputable section

section

/-! Nonvanishing of sufficiently large compact local Gaussian integrals. -/

open _root_.MeasureTheory
open scoped Classical _root_.Topology

theorem compactQuadratic_locallyConstant
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k]
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (U : OpenAddSubgroup k) (a : k) :
    IsLocallyConstant (QuadraticFourier.Construction.compactQuadraticFunction ψ U a) := by
  have hp : IsLocallyConstant (fun x : k => ψ (a * x ^ 2 / 2)) :=
    (NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc).comp_continuous (by fun_prop)
  have h := (CompactCharacter.Construction.subgroup_indicator_locallyConstant U).mul hp
  convert! h using 1
  funext x
  by_cases hx : x ∈ U <;> simp [QuadraticFourier.Construction.compactQuadraticFunction, hx]

theorem compactQuadratic_compactSupport
    {k : Type} [NormedField k]
    (ψ : AddChar k ℂ) (U : OpenAddSubgroup k) (hU : IsCompact (U : Set k)) (a : k) :
    HasCompactSupport (QuadraticFourier.Construction.compactQuadraticFunction ψ U a) := by
  apply HasCompactSupport.intro hU
  intro x hx
  simp [QuadraticFourier.Construction.compactQuadraticFunction, hx]

theorem compactGaussian_ne_zero_of_annihilator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) (U V : OpenAddSubgroup k) (hU : IsCompact (U : Set k))
    (hVU : V ≤ U) (hphase : ∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup) :
    (∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k)) ≠ 0 := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let q : k → ℂ := QuadraticFourier.Construction.compactQuadraticFunction ψ U a
  intro hG
  have hF : FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar q = 0 := by
    funext x
    by_cases hx : x / a ∈ U
    · have h := QuadraticFourier.Construction.scalarFourier_compactQuadratic ψ Measure.addHaar U a (x / a) hx
      have hax : a * (x / a) = x := by field_simp
      rw [hax, hG, mul_zero] at h
      exact h
    · have hnot : ¬ ∀ t ∈ V, ψ (x * t) = 1 := by
        intro hh
        apply hx
        apply (hdual (x / a)).mpr
        intro t ht
        have hax : a * (x / a) = x := by field_simp
        rw [hax]
        exact hh t ht
      push Not at hnot
      obtain ⟨t, ht, htψ⟩ := hnot
      apply QuadraticFourier.Construction.scalarFourier_vanishes_of_translation ψ Measure.addHaar q t x _ htψ
      apply QuadraticFourier.Construction.compactQuadratic_translation ψ U a t (hVU ht) (hphase t ht)
      intro y hy
      exact (hdual y).mp hy t ht
  have hq0 : q 0 = 1 := by simp [q, QuadraticFourier.Construction.compactQuadraticFunction]
  have h := FourierTensor.Construction.scalarFourier_square_reference hNondiscrete ψ hu hc hn
    (compactQuadratic_locallyConstant ψ hu hc U a) (compactQuadratic_compactSupport ψ U hU a) 0
  change FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar (FourierTensor.Construction.scalarFourierIntegral ψ Measure.addHaar q) 0 =
    (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) * q (-0) at h
  rw [hF, neg_zero, hq0, mul_one] at h
  have hzero : (FunctionsMetaplectic.Construction.fourierHaarScaleSquared k ψ : ℂ) = 0 := by
    simpa [FourierTensor.Construction.scalarFourierIntegral] using h.symm
  exact (Complex.ofReal_ne_zero.mpr
    (NonarchimedeanHaar.Construction.nonarchimedean_reference_scale hNondiscrete ψ hu hc hn).1.ne') hzero

theorem exists_quadratic_trivial_subgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (a : k) :
    ∃ V : OpenAddSubgroup k, IsCompact (V : Set k) ∧
      (∃ r : ℝ, 0 < r ∧ (V : Set k) = Metric.closedBall 0 r) ∧
      (∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1) ∧
      (∀ t ∈ V, ∀ s ∈ V, ψ (a * t * s) = 1) := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  have hψ := NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc
  have hp : IsLocallyConstant (fun p : k × k => ψ (a * p.1 * p.2)) :=
    hψ.comp_continuous (by fun_prop)
  have hq : IsLocallyConstant (fun t : k => ψ (a * t ^ 2 / 2)) :=
    hψ.comp_continuous (by fun_prop)
  obtain ⟨ε, hε, hεp⟩ := Metric.eventually_nhds_iff.mp (hp.eventually_eq (0, 0))
  obtain ⟨δ, hδ, hδq⟩ := Metric.eventually_nhds_iff.mp (hq.eventually_eq 0)
  let r : ℝ := min ε δ / 2
  have hr : 0 < r := half_pos (lt_min hε hδ)
  have hrε : r < ε := (half_lt_self (lt_min hε hδ)).trans_le (min_le_left _ _)
  have hrδ : r < δ := (half_lt_self (lt_min hε hδ)).trans_le (min_le_right _ _)
  let V := IsUltrametricDist.closedBall_openAddSubgroup k hr
  have hnorm (t : k) (ht : t ∈ V) : ‖t‖ ≤ r := by
    change t ∈ Metric.closedBall 0 r at ht
    simpa only [Metric.mem_closedBall, dist_zero_right] using ht
  refine ⟨V, isCompact_closedBall 0 r, ⟨r, hr, rfl⟩, ?_, ?_⟩
  · intro t ht
    have hdist : dist t 0 < δ := by simpa only [dist_zero_right] using (hnorm t ht).trans_lt hrδ
    simpa using hδq hdist
  · intro t ht s hs
    have hdist : dist (t, s) (0, 0) < ε := by
      simpa only [Prod.dist_eq, dist_zero_right] using
        (max_le (hnorm t ht) (hnorm s hs)).trans_lt hrε
    simpa using hεp hdist

/-- The required compact Gaussian is obtained from a small subgroup on which the quadratic
character is trivial; no nonvanishing hypothesis is imposed. -/
theorem exists_compactGaussian_domain
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) :
    ∃ U V : OpenAddSubgroup k, IsCompact (U : Set k) ∧ IsCompact (V : Set k) ∧ V ≤ U ∧
      (∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1) ∧
      (∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup) ∧
      (∀ t ∈ V, ∀ y ∉ U, ‖y + t‖ = ‖y‖) ∧
      (∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k)) ≠ 0 := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  obtain ⟨V, hV, ⟨r, _, hrV⟩, hphase, hpair⟩ := exists_quadratic_trivial_subgroup hNondiscrete ψ hu hc a
  obtain ⟨hcomp, hopen⟩ := QuadraticFourier.Construction.scalarAnnihilator_compact_open hNondiscrete ψ hu hc hn V hV
  let W : OpenAddSubgroup k := ⟨QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup, hopen⟩
  let e : k ≃L[k] k :=
    { toLinearEquiv := LinearEquiv.smulOfNeZero k k a ha
      continuous_toFun := continuous_const.mul continuous_id
      continuous_invFun := continuous_const.mul continuous_id }
  let U := W.comap e.toLinearEquiv.toAddEquiv.toAddMonoidHom e.continuous
  have hU : IsCompact (U : Set k) := e.toHomeomorph.isCompact_preimage.mpr hcomp
  have hVU : V ≤ U := by
    intro t ht
    change ∀ s ∈ V, ψ (a * t * s) = 1
    exact hpair t ht
  have hdual (y : k) : y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup := Iff.rfl
  have hradial (t : k) (ht : t ∈ V) (y : k) (hy : y ∉ U) : ‖y + t‖ = ‖y‖ := by
    have htnorm : ‖t‖ ≤ r := by
      have ht' : t ∈ (V : Set k) := ht
      rw [hrV, Metric.mem_closedBall, dist_zero_right] at ht'
      exact ht'
    have hylarge : r < ‖y‖ := by
      by_contra! hynorm
      apply hy
      apply hVU
      change y ∈ (V : Set k)
      rw [hrV, Metric.mem_closedBall, dist_zero_right]
      exact hynorm
    have hlt : ‖t‖ < ‖y‖ := htnorm.trans_lt hylarge
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]
  exact ⟨U, V, hU, hV, hVU, hphase, hdual, hradial,
    compactGaussian_ne_zero_of_annihilator hNondiscrete ψ hu hc hn a ha U V
    hU hVU hphase hdual⟩

theorem exists_nonzero_compactGaussian
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) :
    ∃ U : OpenAddSubgroup k, IsCompact (U : Set k) ∧
      (∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k)) ≠ 0 := by
  obtain ⟨U, _, hU, _, _, _, _, _, hG⟩ := exists_compactGaussian_domain hNondiscrete ψ hu hc hn a ha
  exact ⟨U, hU, hG⟩

end

section

/-! Stabilization of compact local Gaussian integrals by averaging over an annihilator. -/

open _root_.MeasureTheory Filter
open scoped Classical

theorem compactGaussian_stabilizes_of_annihilator
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (a : k) (U V W : OpenAddSubgroup k)
    (hV : IsCompact (V : Set k)) (hW : IsCompact (W : Set k))
    (hVU : V ≤ U) (hUW : U ≤ W)
    (hphase : ∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup) :
    (∫ y in (W : Set k), ψ (a * y ^ 2 / 2) ∂μ) =
      ∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂μ := by
  let q : k → ℂ := fun y => ψ (a * y ^ 2 / 2)
  let g : k → k → ℂ := fun t y =>
    (V : Set k).indicator (fun _ => (1 : ℂ)) t *
      (W : Set k).indicator (fun _ => (1 : ℂ)) y * q (y + t)
  have hg : Continuous g.uncurry := by
    apply (((CompactCharacter.Construction.subgroup_indicator_locallyConstant V).continuous.comp continuous_fst).mul
      ((CompactCharacter.Construction.subgroup_indicator_locallyConstant W).continuous.comp continuous_snd)).mul
    exact hc.comp (by fun_prop)
  have hgs : HasCompactSupport g.uncurry := by
    apply HasCompactSupport.intro (hV.prod hW)
    intro p hp
    by_cases ht : p.1 ∈ V
    · have hy : p.2 ∉ W := fun h => hp ⟨ht, h⟩
      simp [Function.uncurry, g, hy]
    · simp [Function.uncurry, g, ht]
  have hleft : (∫ t, ∫ y, g t y ∂μ ∂μ) =
      (μ.real (V : Set k) : ℂ) * ∫ y in (W : Set k), q y ∂μ := by
    have heq : (fun t => ∫ y, g t y ∂μ) =
        (V : Set k).indicator (fun _ => ∫ y in (W : Set k), q y ∂μ) := by
      funext t
      by_cases ht : t ∈ V
      · rw [Set.indicator_of_mem ht]
        have hfun : g t = fun y => QuadraticFourier.Construction.compactQuadraticFunction ψ W a (y + t) := by
          funext y
          have htW : t ∈ W := hUW (hVU ht)
          have hmem : y + t ∈ W ↔ y ∈ W := W.add_mem_cancel_right htW
          by_cases hy : y ∈ W
          · simp [g, ht, hy, QuadraticFourier.Construction.compactQuadraticFunction, hmem.mpr hy, q]
          · have hyt : y + t ∉ W := fun h => hy (hmem.mp h)
            simp [g, hy, QuadraticFourier.Construction.compactQuadraticFunction, hyt]
        rw [hfun, integral_add_right_eq_self]
        exact integral_indicator W.isOpen.measurableSet
      · simp [g, ht]
    rw [heq, integral_indicator_const _ V.isOpen.measurableSet, Complex.real_smul]
  have hright : (∫ y, ∫ t, g t y ∂μ ∂μ) =
      (μ.real (V : Set k) : ℂ) * ∫ y in (U : Set k), q y ∂μ := by
    have heq : (fun y => ∫ t, g t y ∂μ) =
        (U : Set k).indicator (fun y => (μ.real (V : Set k) : ℂ) * q y) := by
      funext y
      by_cases hyW : y ∈ W
      · have hfun : (fun t => g t y) =
            (V : Set k).indicator (fun t => q y * ψ (a * y * t)) := by
          funext t
          by_cases ht : t ∈ V
          · simp only [g, Set.indicator_of_mem ht, Set.indicator_of_mem hyW, one_mul]
            change ψ (a * (y + t) ^ 2 / 2) = ψ (a * y ^ 2 / 2) * ψ (a * y * t)
            have hsplit : a * (y + t) ^ 2 / 2 = a * y ^ 2 / 2 + a * y * t + a * t ^ 2 / 2 := by
              have h2 : (2 : k) ≠ 0 := by norm_num
              field_simp
              ring
            rw [hsplit, ψ.map_add_eq_mul, ψ.map_add_eq_mul, hphase t ht, mul_one]
          · simp [g, ht]
        rw [hfun, integral_indicator V.isOpen.measurableSet, integral_const_mul,
          QuadraticFourier.Construction.integral_scalarPairing_subgroup]
        by_cases hyU : y ∈ U
        · simp [hyU, (hdual y).mp hyU, mul_comm]
        · have hydual : a * y ∉ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup := fun h => hyU ((hdual y).mpr h)
          simp [hyU, hydual]
      · have hyU : y ∉ U := fun h => hyW (hUW h)
        simp [g, hyW, hyU]
    rw [heq, integral_indicator U.isOpen.measurableSet, integral_const_mul]
  have hswap := integral_integral_swap_of_hasCompactSupport (μ := μ) (ν := μ) hg hgs
  rw [hleft, hright] at hswap
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos μ V hV).ne') hswap

theorem nonarchimedean_gaussian_cutoff_stabilizes
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) :
    ∃ G : ℂ, G ≠ 0 ∧ ∃ R : ℝ, 0 < R ∧ ∀ r : ℝ, R ≤ r →
      (∫ y in Metric.closedBall (0 : k) r, ψ (a * y ^ 2 / 2)
        ∂(Measure.addHaar : Measure k)) = G := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hNondiscrete
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, _, hG⟩ :=
    exists_compactGaussian_domain hNondiscrete ψ hu hc hn a ha
  obtain ⟨R, hR, hbound⟩ := hU.isBounded.exists_pos_norm_le
  refine ⟨_, hG, R, hR, fun r hr => ?_⟩
  let W := IsUltrametricDist.closedBall_openAddSubgroup k (hR.trans_le hr)
  have hUW : U ≤ W := by
    intro x hx
    change x ∈ Metric.closedBall 0 r
    simpa only [Metric.mem_closedBall, dist_zero_right] using (hbound x hx).trans hr
  exact compactGaussian_stabilizes_of_annihilator ψ hc Measure.addHaar a U V W hV
    (isCompact_closedBall 0 r) hVU hUW hphase hdual

end

section

/-! Integrability estimates for Gaussian damping on a locally compact normed field. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology Pointwise NNReal

theorem gaussian_shell_summable
    (q r ε : ℝ) (hq : 0 < q) (hr : 1 < r) (hε : 0 < ε) :
    Summable (fun j : ℕ => q ^ j * Real.exp (-ε * r ^ j)) := by
  have hpos (j : ℕ) : 0 < q ^ j * Real.exp (-ε * r ^ j) := mul_pos (pow_pos hq _) (Real.exp_pos _)
  apply summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
    (Eventually.of_forall fun j => (hpos j).ne')
  have hratio (j : ℕ) :
      ‖q ^ (j + 1) * Real.exp (-ε * r ^ (j + 1))‖ / ‖q ^ j * Real.exp (-ε * r ^ j)‖ =
        q * Real.exp (-(ε * (r - 1) * r ^ j)) := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hpos (j + 1)), abs_of_pos (hpos j)]
    calc
      _ = q * (Real.exp (-ε * r ^ (j + 1)) / Real.exp (-ε * r ^ j)) := by
        rw [pow_succ]
        field_simp
      _ = q * Real.exp (-ε * r ^ (j + 1) - (-ε * r ^ j)) := by rw [Real.exp_sub]
      _ = _ := by congr 2; rw [pow_succ]; ring
  simp only [hratio]
  have hlim : Tendsto (fun j : ℕ => ε * (r - 1) * r ^ j) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hr).const_mul_atTop (mul_pos hε (sub_pos.mpr hr))
  have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hlim).const_mul q
  simpa only [Function.comp_def, mul_zero] using h

theorem haar_closedBall_pow
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (μ : Measure k) [μ.IsAddHaarMeasure] [μ.Regular] (u : kˣ) (j : ℕ) :
    μ.real (Metric.closedBall (0 : k) (‖(u : k)‖ ^ j)) =
      (distribHaarChar k u : ℝ) ^ j * μ.real (Metric.closedBall (0 : k) 1) := by
  have hset : (u ^ j) • Metric.closedBall (0 : k) 1 =
      Metric.closedBall (0 : k) (‖(u : k)‖ ^ j) := by
    change ((u ^ j : kˣ) : k) • Metric.closedBall (0 : k) 1 = _
    rw [smul_closedBall' (u ^ j).ne_zero, smul_zero, mul_one]
    simp
  have h := distribHaarChar_mul μ (u ^ j) (Metric.closedBall (0 : k) 1)
  rw [hset, map_pow] at h
  change (μ (Metric.closedBall (0 : k) (‖(u : k)‖ ^ j))).toReal = _
  rw [← h, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_pow]
  rfl

theorem localField_gaussian_damping_integrable
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (μ : Measure k) [μ.IsAddHaarMeasure] (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun x : k => Real.exp (-ε * ‖x‖ ^ 2)) μ := by
  rcases NormedField.discreteTopology_or_nontriviallyNormedField k with hd | ⟨_, rfl⟩
  · exact (hNondiscrete hd).elim
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨b, hb⟩ := NormedField.exists_one_lt_norm k
  let u : kˣ := Units.mk0 b (norm_pos_iff.mp (zero_lt_one.trans hb))
  let r : ℝ := ‖b‖
  let q : ℝ := distribHaarChar k u
  let f : k → ℝ := fun x => Real.exp (-ε * ‖x‖ ^ 2)
  have hr : 1 < r := hb
  have hq : 0 < q := distribHaarChar_pos
  have hcont : Continuous f := by fun_prop
  let B : ℕ → Set k := fun j => Metric.closedBall 0 (r ^ j)
  let s : ℕ → Set k := fun j => {x | r ^ j ≤ ‖x‖} ∩ B (j + 1)
  have hBi (j : ℕ) : IntegrableOn f (B j) μ := hcont.continuousOn.integrableOn_compact
    (isCompact_closedBall _ _)
  have hsi (j : ℕ) : IntegrableOn f (s j) μ := (hBi (j + 1)).mono_set Set.inter_subset_right
  have hBvol (j : ℕ) : μ.real (B j) = q ^ j * μ.real (B 0) := by
    simpa only [B, pow_zero, q, r, u, Units.val_mk0] using haar_closedBall_pow μ u j
  have hbound (j : ℕ) : (∫ x in s j, ‖f x‖ ∂μ) ≤
      (q * μ.real (B 0)) * (q ^ j * Real.exp (-ε * (r ^ 2) ^ j)) := by
    have hpoint (x : k) (hx : x ∈ s j) : ‖f x‖ ≤ Real.exp (-ε * (r ^ 2) ^ j) := by
      rw [show f x = Real.exp (-ε * ‖x‖ ^ 2) from rfl, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
      have hpow : (r ^ 2) ^ j ≤ ‖x‖ ^ 2 := by
        rw [← pow_mul, Nat.mul_comm 2 j, pow_mul]
        exact pow_le_pow_left₀ (pow_nonneg (zero_lt_one.trans hr).le _) hx.1 2
      nlinarith
    have hfinite : μ (s j) < ⊤ := (measure_mono Set.inter_subset_right).trans_lt
      (isCompact_closedBall (0 : k) (r ^ (j + 1))).measure_lt_top
    have hint := norm_setIntegral_le_of_norm_le_const (f := fun x => ‖f x‖) hfinite
      (fun x hx => by simpa only [norm_norm] using hpoint x hx)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => norm_nonneg (f x)))] at hint
    calc
      _ ≤ Real.exp (-ε * (r ^ 2) ^ j) * μ.real (s j) := hint
      _ ≤ Real.exp (-ε * (r ^ 2) ^ j) * μ.real (B (j + 1)) :=
        mul_le_mul_of_nonneg_left (measureReal_mono Set.inter_subset_right
          (isCompact_closedBall _ _).measure_ne_top) (Real.exp_pos _).le
      _ = _ := by rw [hBvol, pow_succ]; ring
  have hseries : Summable (fun j => ∫ x in s j, ‖f x‖ ∂μ) := by
    have hr2 : 1 < r ^ 2 := by nlinarith
    exact ((gaussian_shell_summable q (r ^ 2) ε hq hr2 hε).mul_left (q * μ.real (B 0))).of_nonneg_of_le
      (fun j => integral_nonneg (fun x => norm_nonneg (f x))) hbound
  have hcover : B 0 ∪ ⋃ j, s j = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : ‖x‖ ≤ 1
    · exact Or.inl (by simpa [B] using hx)
    · have hx1 : 1 ≤ ‖x‖ := (lt_of_not_ge hx).le
      obtain ⟨j, hj, hj'⟩ := exists_nat_pow_near hx1 hr
      refine Or.inr (Set.mem_iUnion.mpr ⟨j, hj, ?_⟩)
      simpa only [B, Metric.mem_closedBall, dist_zero_right] using hj'.le
  have hi := (hBi 0).union (integrableOn_iUnion_of_summable_integral_norm hsi hseries)
  rwa [hcover, integrableOn_univ] at hi

theorem regularizedGaussian_integrable
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (a : k) (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun x : k => (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ (a * x ^ 2 / 2))
      (Measure.addHaar : Measure k) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  have hf := localField_gaussian_damping_integrable hNondiscrete Measure.addHaar ε hε
  have hcont : Continuous (fun x : k => (Real.exp (-ε * ‖x‖ ^ 2) : ℂ) * ψ (a * x ^ 2 / 2)) :=
    (by fun_prop : Continuous (fun x : k => (Real.exp (-ε * ‖x‖ ^ 2) : ℂ))).mul
      (hc.comp (by fun_prop))
  apply hf.mono hcont.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simp only [norm_mul, hu, mul_one, Complex.norm_real, le_refl]

end

section

/-! Cancellation of the integrable Gaussian tail by subgroup averaging. -/

open _root_.MeasureTheory Filter
open scoped Classical

theorem integral_zero_of_scalar_modulation
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (μ : Measure k) [μ.IsAddHaarMeasure]
    (a : k) (U V : OpenAddSubgroup k) (hV : IsCompact (V : Set k))
    (hdual : ∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup)
    {f : k → ℂ} (hf : Continuous f) (hfi : Integrable f μ)
    (hzero : ∀ y ∈ U, f y = 0)
    (hcov : ∀ t ∈ V, ∀ y, f (y + t) = ψ (a * y * t) * f y) :
    (∫ y, f y ∂μ) = 0 := by
  let g : k → k → ℂ := fun t y => (V : Set k).indicator (fun _ => (1 : ℂ)) t * f (y + t)
  have hg : Continuous g.uncurry :=
    ((CompactCharacter.Construction.subgroup_indicator_locallyConstant V).continuous.comp continuous_fst).mul
      (hf.comp (continuous_snd.add continuous_fst))
  have hVi : Integrable ((V : Set k).indicator (fun _ => (1 : ℝ))) μ :=
    memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 V.isOpen.measurableSet 1 (Or.inr hV.measure_ne_top))
  have hgi : Integrable g.uncurry (μ.prod μ) := by
    apply (hVi.mul_prod hfi.norm).mono hg.aestronglyMeasurable
    exact Eventually.of_forall fun p => by
      dsimp only [Function.uncurry]
      by_cases ht : p.1 ∈ V
      · simp [g, ht, hcov p.1 ht p.2, hu]
      · simp [g, ht]
  have hleft : (∫ t, ∫ y, g t y ∂μ ∂μ) = (μ.real (V : Set k) : ℂ) * ∫ y, f y ∂μ := by
    simp_rw [g, integral_const_mul, integral_add_right_eq_self]
    rw [integral_mul_const, integral_indicator_const _ V.isOpen.measurableSet, Complex.real_smul, mul_one]
  have hright : (∫ y, ∫ t, g t y ∂μ ∂μ) = 0 := by
    have hz (y : k) : (∫ t, g t y ∂μ) = 0 := by
      have hfun : (fun t => g t y) =
          (V : Set k).indicator (fun t => ψ (a * y * t) * f y) := by
        funext t
        by_cases ht : t ∈ V
        · simp [g, ht, hcov t ht y]
        · simp [g, ht]
      rw [hfun, integral_indicator V.isOpen.measurableSet, integral_mul_const,
        QuadraticFourier.Construction.integral_scalarPairing_subgroup]
      by_cases hy : y ∈ U
      · rw [hzero y hy, mul_zero]
      · have hy' : a * y ∉ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup := fun h => hy ((hdual y).mpr h)
        rw [ite_eq_right hy', zero_mul]
    simp only [hz, integral_zero]
  have h := integral_integral_swap hgi
  rw [hleft, hright] at h
  exact (mul_eq_zero.mp h).resolve_left
    (Complex.ofReal_ne_zero.mpr (NonarchimedeanFourier.Construction.compact_open_subgroup_real_pos μ V hV).ne')

end

/-! The actual damped Gaussian has a nonzero limit at a nonarchimedean place. -/

open _root_.MeasureTheory Filter
open scoped Classical _root_.Topology

theorem regularizedGaussian_eq_compact_of_domain
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (a : k) (U V : OpenAddSubgroup k) (hV : IsCompact (V : Set k)) (hVU : V ≤ U)
    (hphase : ∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup)
    (hradial : ∀ t ∈ V, ∀ y ∉ U, ‖y + t‖ = ‖y‖)
    (ε : ℝ) (hε : 0 < ε) :
    FunctionsMetaplectic.Construction.regularizedGaussian k ψ a ε =
      ∫ y in (U : Set k), (Real.exp (-ε * ‖y‖ ^ 2) : ℂ) * ψ (a * y ^ 2 / 2)
        ∂(Measure.addHaar : Measure k) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let F : k → ℂ := fun y => (Real.exp (-ε * ‖y‖ ^ 2) : ℂ) * ψ (a * y ^ 2 / 2)
  let f : k → ℂ := (U : Set k)ᶜ.indicator F
  have hFi : Integrable F (Measure.addHaar : Measure k) :=
    regularizedGaussian_integrable hNondiscrete ψ hu hc a ε hε
  have hFcont : Continuous F := (by fun_prop : Continuous (fun y : k =>
    (Real.exp (-ε * ‖y‖ ^ 2) : ℂ))).mul (hc.comp (by fun_prop))
  have hfcont : Continuous f := by
    have h := (CompactApproximation.Construction.clopen_indicator_locallyConstant
      (show IsClopen (U : Set k)ᶜ from ⟨U.isOpen.isClosed_compl, U.isClosed.isOpen_compl⟩)).continuous.mul hFcont
    convert! h using 1
    funext y
    by_cases hy : y ∈ U <;> simp [f, hy]
  have hfi : Integrable f (Measure.addHaar : Measure k) := hFi.indicator U.isOpen.measurableSet.compl
  have hzero : ∀ y ∈ U, f y = 0 := fun y hy => by simp [f, hy]
  have hcov : ∀ t ∈ V, ∀ y, f (y + t) = ψ (a * y * t) * f y := by
    intro t ht y
    have hmem : y + t ∈ U ↔ y ∈ U := U.add_mem_cancel_right (hVU ht)
    by_cases hy : y ∈ U
    · simp [f, hy, hmem.mpr hy]
    · have hyt : y + t ∉ U := fun h => hy (hmem.mp h)
      simp only [f, Set.indicator_of_mem (show y ∈ (U : Set k)ᶜ from hy),
        Set.indicator_of_mem (show y + t ∈ (U : Set k)ᶜ from hyt), F]
      rw [hradial t ht y hy]
      have hsplit : a * (y + t) ^ 2 / 2 = a * y ^ 2 / 2 + a * y * t + a * t ^ 2 / 2 := by
        have h2 : (2 : k) ≠ 0 := by norm_num
        field_simp
        ring
      rw [hsplit, ψ.map_add_eq_mul, ψ.map_add_eq_mul, hphase t ht, mul_one]
      ring
  have htail := integral_zero_of_scalar_modulation ψ hu Measure.addHaar a U V hV hdual hfcont hfi hzero hcov
  rw [show f = (U : Set k)ᶜ.indicator F from rfl, integral_indicator U.isOpen.measurableSet.compl] at htail
  have h := integral_add_compl U.isOpen.measurableSet hFi
  rw [htail, add_zero] at h
  exact h.symm

theorem regularizedGaussian_tendsto_compact_of_domain
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (a : k)
    (U V : OpenAddSubgroup k) (hU : IsCompact (U : Set k)) (hV : IsCompact (V : Set k))
    (hVU : V ≤ U) (hphase : ∀ t ∈ V, ψ (a * t ^ 2 / 2) = 1)
    (hdual : ∀ y, y ∈ U ↔ a * y ∈ QuadraticFourier.Construction.scalarAnnihilator ψ V.toAddSubgroup)
    (hradial : ∀ t ∈ V, ∀ y ∉ U, ‖y + t‖ = ‖y‖) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k))) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let G : ℂ := ∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k)
  let μ : Measure k := (Measure.addHaar : Measure k).restrict U
  let : IsFiniteMeasure μ := ⟨by
    change (Measure.addHaar : Measure k).restrict (U : Set k) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact hU.measure_lt_top⟩
  have hcompact : Tendsto (fun ε : ℝ => ∫ y, (Real.exp (-ε * ‖y‖ ^ 2) : ℂ) * ψ (a * y ^ 2 / 2) ∂μ)
      (𝓝[>] (0 : ℝ)) (𝓝 G) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ))
    · exact Eventually.of_forall fun ε =>
        ((by fun_prop : Continuous (fun y : k => (Real.exp (-ε * ‖y‖ ^ 2) : ℂ))).mul
          (hc.comp (by fun_prop))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
      exact Eventually.of_forall fun y => by
        rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) (sq_nonneg _)
    · exact integrable_const 1
    · exact Eventually.of_forall fun y => by
        have h : Continuous (fun ε : ℝ => (Real.exp (-ε * ‖y‖ ^ 2) : ℂ) * ψ (a * y ^ 2 / 2)) := by fun_prop
        simpa using (h.continuousAt (x := (0 : ℝ))).tendsto.mono_left
          (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  have hlim : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 G) := by
    apply hcompact.congr'
    filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ioi 0)] with ε hε
    exact (regularizedGaussian_eq_compact_of_domain hNondiscrete ψ hu hc a U V hV hVU hphase hdual hradial ε hε).symm
  exact hlim

theorem nonarchimedean_gaussian_limit_nonzero
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : k) (ha : a ≠ 0) :
    Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian k ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral k ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral k ψ a ≠ 0 := by
  obtain ⟨U, V, hU, hV, hVU, hphase, hdual, hradial, hG⟩ :=
    exists_compactGaussian_domain hNondiscrete ψ hu hc hn a ha
  have hlim := regularizedGaussian_tendsto_compact_of_domain hNondiscrete ψ hu hc a
    U V hU hV hVU hphase hdual hradial
  have hGval : FunctionsMetaplectic.Construction.gaussianIntegral k ψ a =
      ∫ y in (U : Set k), ψ (a * y ^ 2 / 2) ∂(Measure.addHaar : Measure k) := hlim.limUnder_eq
  exact ⟨hGval.symm ▸ hlim, hGval.symm ▸ hG⟩

end

end OAI.RepresentationTheory.Weil.Local.GaussianCompact.Construction
