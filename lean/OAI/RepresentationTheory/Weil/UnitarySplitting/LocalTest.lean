import OAI.RepresentationTheory.Weil.UnitarySplitting.Weak

/-! # Local Test -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest.Construction

noncomputable section

section

/-! Nonzero vectors in the actual Bruhat space. The local-field case
distinction is kept separate from these explicit analytic constructions. -/

open Filter
open scoped _root_.Topology SchwartzMap

def ultraTestVector (F : Type) [NormedField F] [LocallyCompactSpace F]
    [IsUltrametricDist F] (hF : ¬ DiscreteTopology F) (d : ℕ) : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d := by
  let : ProperSpace F := TestSpaceAnalysis.Construction.localField_proper F hF
  let U := Metric.closedBall (0 : Local.FunctionsMetaplectic.Construction.Position F d) 1
  have hU : IsClopen U := IsUltrametricDist.isClopen_closedBall _ one_ne_zero
  let f := LocallyConstant.charFn ℂ hU
  refine ⟨f, Local.FunctionsMetaplectic.Construction.compact_locallyConstant_mem f.isLocallyConstant ?_⟩
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Local.FunctionsMetaplectic.Construction.Position F d) 1)
  intro x hx
  exact Set.indicator_of_notMem hx 1

theorem ultraTestVector_at_zero (F : Type) [NormedField F] [LocallyCompactSpace F]
    [IsUltrametricDist F] (hF : ¬ DiscreteTopology F) (d : ℕ) :
    (ultraTestVector F hF d).val 0 = 1 := by
  change (Metric.closedBall (0 : Local.FunctionsMetaplectic.Construction.Position F d) 1).indicator
    (fun _ => (1 : ℂ)) 0 = 1
  simp

theorem ultraTestVector_ne_zero (F : Type) [NormedField F] [LocallyCompactSpace F]
    [IsUltrametricDist F] (hF : ¬ DiscreteTopology F) (d : ℕ) :
    ultraTestVector F hF d ≠ 0 := by
  intro h
  have hh := ultraTestVector_at_zero F hF d
  rw [h] at hh
  exact zero_ne_one hh

theorem exists_real_schwartz_nonzero (d : ℕ) :
    ∃ f : SchwartzMap (Fin d → ℝ) ℂ, f 0 = 1 := by
  obtain ⟨f, -, hc, hd, -, hf⟩ :=
    exists_contDiff_tsupport_subset (x := (0 : Fin d → ℝ)) (n := ⊤)
      (s := Set.univ) Filter.univ_mem
  have hs : HasCompactSupport (Complex.ofRealCLM ∘ f) := hc.comp_left rfl
  refine ⟨hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hd), ?_⟩
  change (f 0 : ℂ) = 1
  simp [hf]

theorem exists_test_nonzero_of_real_coordinates
    {F : Type} [NormedField F] {d r : ℕ}
    (e : (Fin r → ℝ) ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F d) :
    ∃ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d, f ≠ 0 := by
  obtain ⟨φ, hφ⟩ := exists_real_schwartz_nonzero r
  refine ⟨⟨(fun x => φ (e.symm x)), Local.FunctionsMetaplectic.Construction.schwartz_coordinate_mem e φ⟩, ?_⟩
  intro h
  have hh := congrArg (fun f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d => f.val 0) h
  have hh' : φ 0 = 0 := by simpa using hh
  rw [hφ] at hh'
  exact one_ne_zero hh'

theorem circleScalar_injective_ultra
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    [IsUltrametricDist F] (hF : ¬ DiscreteTopology F)
    {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) :=
  Weak.Construction.circleScalar_injective_of_test σ H K c ψ
    (ultraTestVector F hF (m * n)) (ultraTestVector_ne_zero F hF (m * n))

theorem circleScalar_injective_of_real_coordinates
    {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    {m n r : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ)
    (e : (Fin r → ℝ) ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F (m * n)) :
    Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) := by
  obtain ⟨f, hf⟩ := exists_test_nonzero_of_real_coordinates e
  exact Weak.Construction.circleScalar_injective_of_test σ H K c ψ f hf

end

section

/-! A complete locally compact characteristic-zero normed field is either
ultrametric or admits finite-dimensional real additive coordinates. This is
the part of the local-field dichotomy needed for nonzero Bruhat vectors. -/

open Filter
open scoped _root_.Topology

variable (F : Type) [NormedField F] [CharZero F]

def rationalNorm : AbsoluteValue ℚ ℝ where
  toFun q := ‖(q : F)‖
  map_mul' q r := by simp [norm_mul]
  nonneg' q := norm_nonneg _
  eq_zero' q := by simp
  add_le' q r := by simpa using norm_add_le (q : F) (r : F)

theorem rationalCast_uniformContinuous_of_unbounded
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) :
    UniformContinuous (Rat.castHom F : ℚ → F) := by
  have hh : ¬ ∀ n : ℕ, rationalNorm F n ≤ 1 := by
    simpa [rationalNorm] using h
  have he := Rat.AbsoluteValue.equiv_real_of_unbounded hh
  obtain ⟨s, hs, heq⟩ := AbsoluteValue.isEquiv_iff_exists_rpow_eq.mp he.symm
  have hp (q : ℚ) : ‖(q : F)‖ = ‖q‖ ^ s := by
    have hq := congrFun heq q
    simpa [rationalNorm, Rat.AbsoluteValue.real_eq_abs, ← Real.norm_eq_abs,
      Rat.norm_cast_real] using hq.symm
  apply uniformContinuous_of_continuousAt_zero (Rat.castHom F).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  change Tendsto (fun q : ℚ => ‖(q : F)‖) (𝓝 0) (𝓝 0)
  simp_rw [hp]
  have hc : ContinuousAt (fun q : ℚ => ‖q‖ ^ s) 0 :=
    continuous_norm.continuousAt.rpow_const (Or.inr hs.le)
  simpa [Real.zero_rpow hs.ne'] using hc.tendsto

variable [CompleteSpace F]

def realEmbeddingOfUnbounded (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) : ℝ →+* F :=
  IsDenseInducing.extendRingHom
    (i := Rat.castHom ℝ) (f := Rat.castHom F)
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (rationalCast_uniformContinuous_of_unbounded F h)

theorem realEmbeddingOfUnbounded_continuous
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) :
    Continuous (realEmbeddingOfUnbounded F h) :=
  (uniformContinuous_uniformly_extend
    Rat.isUniformEmbedding_coe_real.isUniformInducing Rat.denseRange_cast
    (rationalCast_uniformContinuous_of_unbounded F h)).continuous

theorem exists_real_coordinates_of_unbounded [LocallyCompactSpace F]
    (h : ¬ ∀ n : ℕ, ‖(n : F)‖ ≤ 1) (d : ℕ) :
    ∃ r : ℕ, Nonempty ((Fin r → ℝ) ≃ₜ+ Local.FunctionsMetaplectic.Construction.Position F d) := by
  let : Algebra ℝ F := (realEmbeddingOfUnbounded F h).toAlgebra
  let : ContinuousSMul ℝ F := continuousSMul_of_algebraMap ℝ F
    (realEmbeddingOfUnbounded_continuous F h)
  let : FiniteDimensional ℝ F := FiniteDimensional.of_locallyCompactSpace ℝ
  let b := Module.finBasis ℝ (Local.FunctionsMetaplectic.Construction.Position F d)
  exact ⟨Module.finrank ℝ (Local.FunctionsMetaplectic.Construction.Position F d), ⟨b.equivFunL.symm.toContinuousAddEquiv⟩⟩

theorem exists_test_nonzero [LocallyCompactSpace F]
    (hF : ¬ DiscreteTopology F) (d : ℕ) :
    ∃ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat F d, f ≠ 0 := by
  by_cases h : ∀ n : ℕ, ‖(n : F)‖ ≤ 1
  · let : IsUltrametricDist F :=
      IsUltrametricDist.isUltrametricDist_of_forall_norm_natCast_le_one h
    exact ⟨ultraTestVector F hF d, ultraTestVector_ne_zero F hF d⟩
  · obtain ⟨r, ⟨e⟩⟩ := exists_real_coordinates_of_unbounded F h d
    exact exists_test_nonzero_of_real_coordinates e

theorem circleScalar_injective
    {E : Type} [NormedField E] [Algebra F E]
    [LocallyCompactSpace F] [MeasurableSpace F] [BorelSpace F]
    (hF : ¬ DiscreteTopology F) {m n : ℕ} (σ : E ≃ₐ[F] E)
    (H : Matrix (Fin m) (Fin m) E) (K : Matrix (Fin n) (Fin n) E)
    (c : Oscillator.Construction.SymplecticFrame σ H K) (ψ : AddChar F ℂ) :
    Function.Injective (Oscillator.Construction.circleScalar σ H K c ψ) := by
  obtain ⟨f, hf⟩ := exists_test_nonzero F hF (m * n)
  exact Weak.Construction.circleScalar_injective_of_test σ H K c ψ f hf

end

/-! The elementary no-small-subgroups argument needed to make continuous
additive characters locally constant over ultrametric fields. -/

open scoped BigOperators _root_.Topology

theorem complex_eq_one_of_powers_near_one (z : ℂ)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  by_contra hz
  have hzpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖z - 1‖)
  have hnpos : 0 < (n : ℝ) := lt_trans (by positivity) hn
  let S : ℂ := ∑ i ∈ Finset.range n, z ^ i
  have hsum : ‖S - (n : ℂ)‖ ≤ (n : ℝ) / 2 := by
    have heq : S - (n : ℂ) = ∑ i ∈ Finset.range n, (z ^ i - 1) := by
      simp [S, Finset.sum_sub_distrib]
    rw [heq]
    calc
      _ ≤ ∑ i ∈ Finset.range n, ‖z ^ i - 1‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ Finset.range n, (1 / 2 : ℝ) :=
        Finset.sum_le_sum (fun i _ => (h i).le)
      _ = (n : ℝ) / 2 := by simp [div_eq_mul_inv]
  have hlower : (n : ℝ) / 2 ≤ ‖S‖ := by
    have ht := norm_sub_norm_le (n : ℂ) S
    rw [norm_sub_rev] at ht
    simp only [Complex.norm_natCast] at ht
    linarith
  have hgeom : S * (z - 1) = z ^ n - 1 := geom_sum_mul z n
  have hup : ‖S‖ * ‖z - 1‖ < 1 / 2 := by
    rw [← norm_mul, hgeom]
    exact h n
  have hnlarge : 1 < (n : ℝ) * ‖z - 1‖ := (div_lt_iff₀ hzpos).mp hn
  nlinarith [mul_le_mul_of_nonneg_right hlower hzpos.le]

theorem additiveCharacter_locallyConstant_ultra
    {F : Type} [NormedField F] [IsUltrametricDist F]
    (ψ : AddChar F ℂ) (hψ : Continuous (fun x : F => ψ x)) :
    IsLocallyConstant (fun x : F => ψ x) := by
  obtain ⟨ε, hε, hsmall⟩ := Metric.continuousAt_iff.mp (hψ.continuousAt (x := 0))
    (1 / 2) (by norm_num)
  have hker (x : F) (hx : ‖x‖ < ε) : ψ x = 1 := by
    apply complex_eq_one_of_powers_near_one
    intro n
    have hbound : ‖n • x‖ ≤ ‖x‖ := by
      rw [nsmul_eq_mul, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg x)
        (IsUltrametricDist.norm_natCast_le_one F n)
    have hh := hsmall (by simpa only [dist_zero_right] using lt_of_le_of_lt hbound hx)
    simpa only [AddChar.map_nsmul_eq_pow, AddChar.map_zero_eq_one, dist_eq_norm] using hh
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  filter_upwards [Metric.ball_mem_nhds x hε] with y hy
  have hh := ψ.map_add_eq_mul (y - x) x
  rw [sub_add_cancel, hker (y - x) (by simpa only [Metric.mem_ball, dist_eq_norm] using hy),
    one_mul] at hh
  exact hh

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.LocalTest.Construction
