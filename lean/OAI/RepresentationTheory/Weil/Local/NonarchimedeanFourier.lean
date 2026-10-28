import OAI.RepresentationTheory.Weil.Local.NonarchimedeanInversion

/-! # Nonarchimedean Fourier -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier.Construction

noncomputable section

section

/-! A compact-domain Fubini formula for the square of the local Fourier integral. -/

open _root_.MeasureTheory Filter
open scoped Classical

theorem fourier_square_compact_kernel
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hfreq : tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x =
      ∫ y, f y * FunctionsMetaplectic.Construction.fourierIntegral ψ μ ((U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))) (x + y) ∂μ := by
  let A : FunctionsMetaplectic.Construction.Position k n → ℂ := (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ))
  let g : FunctionsMetaplectic.Construction.Position k n → FunctionsMetaplectic.Construction.Position k n → ℂ :=
    fun ξ y => A ξ * f y * ψ (-FunctionsMetaplectic.Construction.dot ξ (y + x))
  have hA : Continuous A := (CompactCharacter.Construction.subgroup_indicator_locallyConstant U).continuous
  have hg : Continuous g.uncurry := by
    apply ((hA.comp continuous_fst).mul (hf.comp continuous_snd)).mul
    apply hc.comp
    unfold FunctionsMetaplectic.Construction.dot
    fun_prop
  have hgs : HasCompactSupport g.uncurry := by
    apply HasCompactSupport.intro (hU.prod hs)
    intro p hp
    change A p.1 * f p.2 * ψ (-FunctionsMetaplectic.Construction.dot p.1 (p.2 + x)) = 0
    by_cases hp1 : p.1 ∈ U
    · have hp2 : p.2 ∉ tsupport f := fun h => hp ⟨hp1, h⟩
      rw [image_eq_zero_of_notMem_tsupport hp2, mul_zero, zero_mul]
    · simp [A, hp1]
  calc
    _ = ∫ ξ, A ξ * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f ξ * ψ (-FunctionsMetaplectic.Construction.dot x ξ) ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        by_cases hξ : ξ ∈ U
        · simp [A, hξ]
        · have hzero : FunctionsMetaplectic.Construction.fourierIntegral ψ μ f ξ = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hξ (hfreq h))
          simp [A, hξ, hzero]
    _ = ∫ ξ, ∫ y, g ξ y ∂μ ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ξ => by
        dsimp only
        rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_const_mul, ← integral_mul_const]
        apply integral_congr_ae
        exact Eventually.of_forall fun y => by
          dsimp only
          have hp : -FunctionsMetaplectic.Construction.dot ξ (y + x) = -FunctionsMetaplectic.Construction.dot ξ y + -FunctionsMetaplectic.Construction.dot x ξ := by
            rw [FourierTools.Construction.dot_comm x ξ]
            simp [FunctionsMetaplectic.Construction.dot, Pi.add_apply, mul_add, Finset.sum_add_distrib, add_comm]
          change _ = A ξ * f y * ψ (-FunctionsMetaplectic.Construction.dot ξ (y + x))
          rw [hp, ψ.map_add_eq_mul]
          ring
    _ = ∫ y, ∫ ξ, g ξ y ∂μ ∂μ := integral_integral_swap_of_hasCompactSupport hg hgs
    _ = _ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        dsimp only
        rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun ξ => by
          change A ξ * f y * ψ (-FunctionsMetaplectic.Construction.dot ξ (y + x)) = f y * (A ξ * ψ (-FunctionsMetaplectic.Construction.dot (x + y) ξ))
          rw [FourierTools.Construction.dot_comm ξ (y + x), add_comm y x]
          ring

theorem fourier_square_subgroup_value
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n)) (hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)))
    (hann : MeasurableSet (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)))
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (hfreq : tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U)
    (hperiod : ∀ t ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup, ∀ y, f (y + t) = f y)
    (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x =
      (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) *
        (μ.real (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) * f (-x) := by
  rw [fourier_square_compact_kernel ψ hc μ U hU hf hs hfreq]
  simp_rw [CompactCharacter.Construction.fourier_indicator_subgroup]
  rw [← integral_sub_right_eq_self
    (fun y => f y * if x + y ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup
      then (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0) x]
  have heq : (fun z => f (z - x) * if x + (z - x) ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup
      then (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) else 0) =
      (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)).indicator
        (fun _ => (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) * f (-x)) := by
    funext z
    have hxz : x + (z - x) = z := by abel
    rw [hxz]
    by_cases hz : z ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup
    · have hfz : f (z - x) = f (-x) := by
        simpa only [sub_eq_add_neg, add_comm z (-x)] using hperiod z hz (-x)
      simp [hz, hfz, mul_comm]
    · simp [hz]
  rw [heq, integral_indicator_const _ hann, Complex.real_smul]
  ring

end

section

/-! The unnormalized Fourier square has one positive scale on the nonarchimedean test space. -/

open _root_.MeasureTheory
open scoped Classical

theorem additiveAnnihilator_antitone
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    {U V : AddSubgroup (FunctionsMetaplectic.Construction.Position k n)} (h : U ≤ V) :
    CompactCharacter.Construction.additiveAnnihilator ψ V ≤ CompactCharacter.Construction.additiveAnnihilator ψ U :=
  fun _ hx y hy => hx y (h hy)

theorem exists_compact_open_supergroup
    {E : Type*} [NormedAddCommGroup E] [IsUltrametricDist E] [ProperSpace E]
    (K : Set E) (hK : IsCompact K) :
    ∃ U : OpenAddSubgroup E, IsCompact (U : Set E) ∧ K ⊆ U := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_le
  let U := IsUltrametricDist.closedBall_openAddSubgroup E hR
  refine ⟨U, isCompact_closedBall 0 R, ?_⟩
  intro x hx
  change x ∈ Metric.closedBall 0 R
  simpa only [Metric.mem_closedBall, dist_zero_right] using hbound x hx

theorem compact_open_subgroup_real_pos
    {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (U : OpenAddSubgroup E)
    (hU : IsCompact (U : Set E)) : 0 < μ.real (U : Set E) := by
  exact ENNReal.toReal_pos
    (Measure.measure_pos_of_nonempty_interior μ
      (by rw [U.isOpen.interior_eq]; exact ⟨0, U.zero_mem⟩)).ne'
    hU.measure_ne_top

theorem exists_common_adapted_frequency_subgroup
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    {f g : FunctionsMetaplectic.Construction.Position k n → ℂ}
    (hf : IsLocallyConstant f) (hsf : HasCompactSupport f)
    (hg : IsLocallyConstant g) (hsg : HasCompactSupport g) :
    ∃ U : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n), IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)) ∧
      tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) ⊆ U ∧
      tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μ g) ⊆ U ∧
      (∀ t ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, f (x + t) = f x) ∧
      (∀ t ∈ CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup, ∀ x, g (x + t) = g x) := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  obtain ⟨V, hV, hfreqf, hperf⟩ :=
    NonarchimedeanInversion.Construction.exists_adapted_frequency_subgroup hNondiscrete ψ hn μ hf hsf
  obtain ⟨W, hW, hfreqg, hperg⟩ :=
    NonarchimedeanInversion.Construction.exists_adapted_frequency_subgroup hNondiscrete ψ hn μ hg hsg
  obtain ⟨U, hU, hsup⟩ := exists_compact_open_supergroup _ (hV.union hW)
  have hVU : V.toAddSubgroup ≤ U.toAddSubgroup := fun _ hx => hsup (Or.inl hx)
  have hWU : W.toAddSubgroup ≤ U.toAddSubgroup := fun _ hx => hsup (Or.inr hx)
  exact ⟨U, hU, fun _ hx => hVU (hfreqf hx), fun _ hx => hWU (hfreqg hx),
    fun _ ht => hperf _ (additiveAnnihilator_antitone ψ hVU ht),
    fun _ ht => hperg _ (additiveAnnihilator_antitone ψ hWU ht)⟩

/-- A single positive constant works for every compact locally constant test function. -/
theorem nonarchimedean_fourier_square_positive_scalar
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : FunctionsMetaplectic.Construction.Position k n → ℂ,
      IsLocallyConstant f → HasCompactSupport f → ∀ x,
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x = (c : ℂ) * f (-x) := by
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hNondiscrete
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let V := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  have hV : IsCompact (V : Set (FunctionsMetaplectic.Construction.Position k n)) := isCompact_closedBall 0 1
  let f₀ : FunctionsMetaplectic.Construction.Position k n → ℂ := (V : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1)
  have hf₀ : IsLocallyConstant f₀ := CompactCharacter.Construction.subgroup_indicator_locallyConstant V
  have hs₀ : HasCompactSupport f₀ := CompactCharacter.Construction.subgroup_indicator_compactSupport V hV
  have hzero : f₀ 0 = 1 := by simp [f₀]
  obtain ⟨U₀, hU₀, hfreq₀, hper₀⟩ :=
    NonarchimedeanInversion.Construction.exists_adapted_frequency_subgroup hNondiscrete ψ hn μ hf₀ hs₀
  obtain ⟨hcomp₀, hopen₀⟩ :=
    CompactCharacter.Construction.additiveAnnihilator_compact_open hNondiscrete ψ hu hc hn μ U₀ hU₀
  let W₀ : OpenAddSubgroup (FunctionsMetaplectic.Construction.Position k n) :=
    ⟨CompactCharacter.Construction.additiveAnnihilator ψ U₀.toAddSubgroup, hopen₀⟩
  let c : ℝ := μ.real (U₀ : Set (FunctionsMetaplectic.Construction.Position k n)) * μ.real (W₀ : Set (FunctionsMetaplectic.Construction.Position k n))
  have hcpos : 0 < c := mul_pos (compact_open_subgroup_real_pos μ U₀ hU₀)
    (compact_open_subgroup_real_pos μ W₀ hcomp₀)
  have hcvalue : FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f₀) 0 = (c : ℂ) := by
    rw [fourier_square_subgroup_value ψ hc μ U₀ hU₀ hopen₀.measurableSet
      hf₀.continuous hs₀ hfreq₀ hper₀]
    change (μ.real (U₀ : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) *
      (μ.real (CompactCharacter.Construction.additiveAnnihilator ψ U₀.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) * f₀ (-0) =
      ((μ.real (U₀ : Set (FunctionsMetaplectic.Construction.Position k n)) *
        μ.real (CompactCharacter.Construction.additiveAnnihilator ψ U₀.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) : ℝ) : ℂ)
    simp only [neg_zero, hzero, mul_one, Complex.ofReal_mul]
  refine ⟨c, hcpos, fun f hf hs x => ?_⟩
  obtain ⟨U, hU, hfreqf, hfreqg, hperf, hperg⟩ :=
    exists_common_adapted_frequency_subgroup hNondiscrete ψ hn μ hf hs hf₀ hs₀
  obtain ⟨_, hopen⟩ := CompactCharacter.Construction.additiveAnnihilator_compact_open hNondiscrete ψ hu hc hn μ U hU
  have hscale : (μ.real (U : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) *
      (μ.real (CompactCharacter.Construction.additiveAnnihilator ψ U.toAddSubgroup : Set (FunctionsMetaplectic.Construction.Position k n)) : ℂ) = (c : ℂ) := by
    have h := fourier_square_subgroup_value ψ hc μ U hU hopen.measurableSet
      hf₀.continuous hs₀ hfreqg hperg 0
    simpa only [neg_zero, hzero, mul_one, hcvalue] using h.symm
  rw [fourier_square_subgroup_value ψ hc μ U hU hopen.measurableSet
    hf.continuous hs hfreqf hperf, hscale]

end

section

/-! Plancherel from the concrete Fourier-square identity. -/

open _root_.MeasureTheory
open scoped ComplexConjugate InnerProductSpace

theorem fourierIntegral_inner_swap
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [SigmaFinite μ]
    {f g : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∫ x, inner ℂ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x) (g x) ∂μ) =
      ∫ x, inner ℂ (f x) (FunctionsMetaplectic.Construction.fourierIntegral ψ μ g (-x)) ∂μ := by
  have hflip : VectorFourier.fourierIntegral (FourierTools.Construction.circleCharacter ψ hu) μ
      (-(dotProductBilin k k).flip) g = fun x => FunctionsMetaplectic.Construction.fourierIntegral ψ μ g (-x) := by
    funext x
    unfold VectorFourier.fourierIntegral FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change ψ (-(-FunctionsMetaplectic.Construction.dot x y)) * g y = g y * ψ (-FunctionsMetaplectic.Construction.dot (-x) y)
      simp [FunctionsMetaplectic.Construction.dot, Finset.sum_neg_distrib, mul_comm]
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (innerSL ℂ) (FourierTools.Construction.circleCharacter_continuous ψ hu hc)
    (FourierTools.Construction.dotProductBilin_continuous n) hf hg
  rw [hflip, ← FourierTools.Construction.fourierIntegral_eq_vectorFourier ψ hu] at h
  exact h

theorem fourierIntegral_norm_sq_of_square
    {k : Type} [NormedField k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [SigmaFinite μ]
    {f : FunctionsMetaplectic.Construction.Position k n → ℂ} (hf : Integrable f μ)
    (hF : Integrable (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) μ) (c : ℝ)
    (hsquare : ∀ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x = (c : ℂ) * f (-x)) :
    (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x‖ ^ 2 ∂μ) = c * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  have h := fourierIntegral_inner_swap ψ hu hc μ hf hF
  simp_rw [hsquare, neg_neg, ← smul_eq_mul, inner_smul_right,
    inner_self_eq_norm_sq_to_K] at h
  simp_rw [← RCLike.ofReal_pow] at h
  rw [integral_const_mul, integral_ofReal, integral_ofReal] at h
  apply RCLike.ofReal_injective (K := ℂ)
  rw [RCLike.ofReal_mul]
  exact h

/-- Plancherel for compact locally constant functions, with the same positive scale as inversion. -/
theorem nonarchimedean_fourier_square_and_plancherel
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ c : ℝ, 0 < c ∧ ∀ f : FunctionsMetaplectic.Construction.Position k n → ℂ,
      IsLocallyConstant f → HasCompactSupport f →
        (∀ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) x = (c : ℂ) * f (-x)) ∧
        (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ f x‖ ^ 2 ∂μ) = c * ∫ x, ‖f x‖ ^ 2 ∂μ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨c, hcpos, hsquare⟩ :=
    nonarchimedean_fourier_square_positive_scalar hNondiscrete n ψ hu hc hn μ
  refine ⟨c, hcpos, fun f hf hs => ⟨hsquare f hf hs, ?_⟩⟩
  apply fourierIntegral_norm_sq_of_square ψ hu hc μ
    (hf.continuous.integrable_of_hasCompactSupport hs) _ c (hsquare f hf hs)
  exact (CompactCharacter.Construction.fourierIntegral_locallyConstant ψ
    (NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc) μ hs).continuous.integrable_of_hasCompactSupport
    (CompactCharacter.Construction.fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hn μ hf hs)

end

/-! A unitary Fourier equivalence on the actual nonarchimedean Bruhat space. -/

open _root_.MeasureTheory

theorem nonarchimedean_heisenberg_mem
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t))
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n := by
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  change (fun x => FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val x) ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n
  simp_rw [LinearIntertwiner.Construction.heisenbergFunction_eq_dot]
  apply FunctionsMetaplectic.Construction.compact_locallyConstant_mem
  · apply ((NonarchimedeanTestSpace.Construction.nonarchimedean_character_locallyConstant ψ hu hc).comp_continuous _).mul
      (hf.comp_continuous (continuous_id.sub continuous_const))
    unfold FunctionsMetaplectic.Construction.dot
    fun_prop
  · exact (hs.comp_homeomorph (Homeomorph.subRight (LinearIntertwiner.Construction.positionPart v))).mul_left

theorem exists_nonarchimedean_unitary_fourier
    {k : Type} [NormedField k] [LocallyCompactSpace k] [IsUltrametricDist k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) (n : ℕ)
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure] :
    ∃ (a : ℝ) (T : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n),
      0 < a ∧
      (∀ f x, (T f).val x = (a : ℂ) * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x) ∧
      (∀ f, (∫ x, ‖(T f).val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  obtain ⟨c, hcpos, hspec⟩ :=
    nonarchimedean_fourier_square_and_plancherel hNondiscrete n ψ hu hc hn μ
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  let F : FunctionsMetaplectic.Construction.schwartzBruhat k n →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n :=
    (FourierTools.Construction.schwartzBruhat_fourierLinearMap n ψ hu hc μ).codRestrict (FunctionsMetaplectic.Construction.schwartzBruhat k n)
      (CompactCharacter.Construction.nonarchimedean_fourier_mem hNondiscrete ψ hu hc hn μ)
  have hF (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
      (F f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x := rfl
  have hsquare (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
      (F (F f)).val x = (c : ℂ) * f.val (-x) := by
    obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
    exact (hspec f.val hf hs).1 x
  have hbij : Function.Bijective F := by
    constructor
    · intro f g heq
      apply Subtype.ext
      funext x
      have h := congrArg (fun z : FunctionsMetaplectic.Construction.schwartzBruhat k n => (F z).val (-x)) heq
      rw [hsquare, hsquare, neg_neg] at h
      exact mul_left_cancel₀ hcn h
    · intro f
      obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
      let r : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨fun x => f.val (-x), FunctionsMetaplectic.Construction.compact_locallyConstant_mem
        (hf.comp_continuous continuous_neg) (hs.comp_homeomorph (Homeomorph.neg _))⟩
      refine ⟨(c : ℂ)⁻¹ • F r, ?_⟩
      apply Subtype.ext
      funext x
      rw [map_smul]
      change (c : ℂ)⁻¹ * (F (F r)).val x = f.val x
      rw [hsquare]
      simp [r, hcn]
  let a : ℝ := (Real.sqrt c)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hcpos)
  let u : ℂˣ := Units.mk0 (a : ℂ) (Complex.ofReal_ne_zero.mpr ha.ne')
  let T := (LinearEquiv.ofBijective F hbij).trans (LinearEquiv.smulOfUnit u)
  have hT (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
      (T f).val x = (a : ℂ) * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x := rfl
  refine ⟨a, T, ha, hT, fun f => ?_⟩
  simp_rw [hT, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  rw [integral_const_mul]
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  rw [(hspec f.val hf hs).2, ← mul_assoc]
  have hscale : a ^ 2 * c = 1 := by
    rw [show a = (Real.sqrt c)⁻¹ from rfl, inv_pow, Real.sq_sqrt hcpos.le,
      inv_mul_cancel₀ hcpos.ne']
  rw [hscale, one_mul]

theorem scalar_fourier_intertwines
    {k : Type} [NormedField k] [LocallyCompactSpace k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [NonarchimedeanAddGroup k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (a : ℂ) (T : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n)
    (hT : ∀ f x, (T f).val x = a * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x)
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v) (T f) (T h) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let hf : FunctionsMetaplectic.Construction.schwartzBruhat k n :=
    ⟨FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val, nonarchimedean_heisenberg_mem ψ hu hc v f⟩
  have hcov : (T hf).val =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v) (T f).val := by
    have heq (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (T g).val = a • FunctionsMetaplectic.Construction.fourierIntegral ψ μ g.val :=
      funext (hT g)
    rw [heq, heq, LinearIntertwiner.Construction.heisenbergFunction_smul]
    change a • FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.heisenbergFunction ψ v f.val) = _
    rw [FourierEquivalence.Construction.fourierIntegral_heisenberg]
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [← hcov]
  change h.val = hf.val ↔ (T h).val = (T hf).val
  constructor
  · intro hh
    rw [Subtype.ext hh]
  · intro hh
    exact congrArg Subtype.val (T.injective (Subtype.ext hh))

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanFourier.Construction
