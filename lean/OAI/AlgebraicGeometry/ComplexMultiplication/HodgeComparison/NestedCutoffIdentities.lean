import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongCutoffGradient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalElliptic

/-! # Nested Cutoff Identities -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffIdentities.CM.Construction

noncomputable section

/-! A cutoff equal to one near the support of another cutoff leaves both
the localized function and its weak metric equation unchanged. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap LineDeriv _root_.Topology

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

theorem cutoffGradientMultiply_coe (b : OrthonormalBasis ι ℝ E) (g : 𝓢(E, ℂ))
    (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), CutoffDifferential.CM.Construction.cutoffGradientMultiply b g u x =
      ∑ i, StrongCutoffGradient.CM.Construction.cutoffGradientInsertion i ((∂_{b i} g : 𝓢(E, ℂ)) x • u x) := by
  rw [StrongCutoffGradient.CM.Construction.cutoffGradientMultiply_sum]
  let term := fun i => (StrongCutoffGradient.CM.Construction.cutoffGradientInsertion i).compLpL 2 (volume : Measure E)
    (CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u)
  have hc : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      term i x = StrongCutoffGradient.CM.Construction.cutoffGradientInsertion i ((∂_{b i} g : 𝓢(E, ℂ)) x • u x) := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(StrongCutoffGradient.CM.Construction.cutoffGradientInsertion i).coeFn_compLpL
      (CutoffDifferential.CM.Construction.schwartzL2Multiply (∂_{b i} g : 𝓢(E, ℂ)) u),
      CutoffDifferential.CM.Construction.schwartzL2Multiply_coe (∂_{b i} g : 𝓢(E, ℂ)) u] with x hT hg
    exact hT.trans (congrArg (StrongCutoffGradient.CM.Construction.cutoffGradientInsertion i) hg)
  filter_upwards [LpComponents.CM.Construction.lp_coe_finsetSum term Finset.univ, hc] with x hs hx
  exact hs.trans (Finset.sum_congr rfl (fun i _ => hx i))

theorem cutoffGradientMultiply_zero_on_locally_one (b : OrthonormalBasis ι ℝ E)
    (η : 𝓢(E, ℂ)) {S : Set E} (hη : ∀ x ∈ S, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ S → CutoffDifferential.CM.Construction.cutoffGradientMultiply b η u x = 0 := by
  filter_upwards [cutoffGradientMultiply_coe b η u] with x hx
  intro hxS
  rw [hx]
  apply Finset.sum_eq_zero
  intro i _
  have hd : (∂_{b i} η : 𝓢(E, ℂ)) x = 0 := by
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, (hη x hxS).fderiv_eq]
    change (fderiv ℝ (Function.const E (1 : ℂ)) x) (b i) = 0
    rw [fderiv_const]
    rfl
  rw [hd, zero_smul, map_zero]

theorem sobolevVectorGradient_cutoff_eq_on (b : OrthonormalBasis ι ℝ E)
    (η : 𝓢(E, ℂ)) {S : Set E} (hη : ∀ x ∈ S, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp ℂ 2 (volume : Measure E)) :
    ∀ᵐ x ∂(volume : Measure E), x ∈ S →
      EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 η u) x = EuclideanGradient.CM.Construction.sobolevVectorGradient b u x := by
  rw [CutoffDifferential.CM.Construction.sobolevVectorGradient_cutoff]
  filter_upwards [Lp.coeFn_add (CutoffDifferential.CM.Construction.cutoffGradientMultiply b η (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u))
      (CutoffDifferential.CM.Construction.schwartzL2Multiply η (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)),
    cutoffGradientMultiply_zero_on_locally_one b η hη
      (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u),
    CutoffDifferential.CM.Construction.schwartzL2Multiply_coe η (EuclideanGradient.CM.Construction.sobolevVectorGradient b u)] with x hadd hK hS
  intro hx
  have hηx : η x = 1 := (hη x hx).eq_of_nhds
  rw [hadd, Pi.add_apply, hK hx, hS, hηx, one_smul, zero_add]

theorem nested_cutoff_energy_eq (b : OrthonormalBasis ι ℝ E)
    (A : E → EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι) (g η : 𝓢(E, ℂ))
    (hη : ∀ x ∈ tsupport g, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u v : Lp ℂ 2 (volume : Measure E)) :
    (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 η u) x))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) =
    (∫ x, inner ℝ (A x (EuclideanGradient.CM.Construction.sobolevVectorGradient b u x))
      (EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x)) := by
  let w : SobolevIs.CM.Construction.supportedH1Coordinates (tsupport g) :=
    ⟨SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v, SobolevSmoothDensity.CM.Construction.sobolevCutoffCLM_mem_supported g (subset_tsupport g) v⟩
  have hw : ∀ᵐ x ∂(volume : Measure E), x ∉ tsupport g →
      EuclideanGradient.CM.Construction.sobolevVectorGradient b (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g v) x = 0 :=
    GradientSupport.CM.Construction.supportedH1VectorGradient_support b isClosed_closure w
  apply integral_congr_ae
  filter_upwards [hw, sobolevVectorGradient_cutoff_eq_on b η hη u] with x hgx hηx
  by_cases hx : x ∈ tsupport g
  · rw [hηx hx]
  · rw [hgx hx, inner_zero_right, inner_zero_right]

omit [Fintype ι] in
theorem sobolevCutoffCLM_nested (n : ℕ) (g η : 𝓢(E, ℂ))
    (hη : ∀ x ∈ tsupport g, (η : E → ℂ) =ᶠ[𝓝 x] 1)
    (u : Lp ℂ 2 (volume : Measure E)) :
    SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM n g (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM n η u) = SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM n g u := by
  apply SobolevCutoffOperator.CM.Construction.sobolevDistributionCLM_injective (n : ℝ)
  simp only [SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM_distribution]
  rw [TemperedDistribution.smulLeftCLM_smulLeftCLM_apply η.hasTemperateGrowth g.hasTemperateGrowth]
  have hmul : (η : E → ℂ) * (g : E → ℂ) = (g : E → ℂ) := by
    funext x
    change η x * g x = g x
    by_cases hx : g x = 0
    · rw [hx, mul_zero]
    · have hηx : η x = 1 := (hη x ((subset_tsupport g) hx)).eq_of_nhds
      rw [hηx, one_mul]
  rw [hmul]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.NestedCutoffIdentities.CM.Construction
