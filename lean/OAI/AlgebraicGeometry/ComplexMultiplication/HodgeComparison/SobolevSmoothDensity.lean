import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevCutoffOperator

/-! # Sobolev Smooth Density -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevSmoothDensity.CM.Construction

noncomputable section

/-! Density of actual Schwartz functions in Sobolev coordinates, and supported
cutoffs as legitimate elements of the completed Dirichlet test space. -/

open _root_.MeasureTheory TemperedDistribution Set
open scoped SchwartzMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

def schwartzBesselPotential (s : ℝ) : 𝓢(E, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ (fun x : E => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))

theorem schwartzBesselPotential_distribution (s : ℝ) (f : 𝓢(E, ℂ)) :
    (schwartzBesselPotential s f : 𝓢'(E, ℂ)) = besselPotential E ℂ s (f : 𝓢'(E, ℂ)) :=
  (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f).symm

theorem schwartzSobolevCoordinate_inverseBessel (s : ℝ) (f : 𝓢(E, ℂ)) :
    SobolevIs.CM.Construction.schwartzSobolevCoordinate s (schwartzBesselPotential (-s) f) = f.toLp 2 (volume : Measure E) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := ℂ) (μ := (volume : Measure E)) (p := 2)))
  change (((Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ s).symm
    ⟨(schwartzBesselPotential (-s) f : 𝓢'(E, ℂ)), (schwartzBesselPotential (-s) f).memSobolev⟩) :
      𝓢'(E, ℂ)) = ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ))
  rw [Bounds.CM.Construction.sobolevCoordinateEquiv_symm_distribution]
  change besselPotential E ℂ s (schwartzBesselPotential (-s) f : 𝓢'(E, ℂ)) =
    ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, ℂ))
  rw [schwartzBesselPotential_distribution,
    besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
    ContinuousLinearMap.id_apply, Lp.toTemperedDistribution_toLp_eq]

theorem schwartzSobolevCoordinate_denseRange (s : ℝ) :
    DenseRange (SobolevIs.CM.Construction.schwartzSobolevCoordinate (E := E) s) := by
  have hsub : Set.range (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure E)) ⊆
      Set.range (SobolevIs.CM.Construction.schwartzSobolevCoordinate (E := E) s) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨schwartzBesselPotential (-s) f, schwartzSobolevCoordinate_inverseBessel s f⟩
  intro u
  exact closure_mono hsub ((SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)) u)

theorem sobolevDistributionCLM_schwartz (s : ℝ) (f : 𝓢(E, ℂ)) :
    SobolevCutoffOperator.CM.Construction.sobolevDistributionCLM s (SobolevIs.CM.Construction.schwartzSobolevCoordinate s f) = (f : 𝓢'(E, ℂ)) := by
  exact congrArg Subtype.val ((Bounds.CM.Construction.sobolevCoordinateEquiv E ℂ s).apply_symm_apply
    ⟨(f : 𝓢'(E, ℂ)), f.memSobolev⟩)

theorem sobolevCutoffCLM_schwartz (n : ℕ) (g f : 𝓢(E, ℂ)) :
    SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM n g (SobolevIs.CM.Construction.schwartzSobolevCoordinate (n : ℝ) f) =
      SobolevIs.CM.Construction.schwartzSobolevCoordinate (n : ℝ) (SchwartzMap.smulLeftCLM ℂ g f) := by
  apply SobolevCutoffOperator.CM.Construction.sobolevDistributionCLM_injective (n : ℝ)
  rw [SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM_distribution, sobolevDistributionCLM_schwartz, sobolevDistributionCLM_schwartz]
  ext φ
  simp only [smulLeftCLM_apply_apply, SchwartzMap.toTemperedDistributionCLM_apply_apply]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    simp only [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth, smul_eq_mul]
    ring)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartz_cutoff_mem_supported (g f : 𝓢(E, ℂ)) {K : Set E}
    (hg : Function.support (g : E → ℂ) ⊆ K) :
    SchwartzMap.smulLeftCLM ℂ g f ∈ SobolevIs.CM.Construction.supportedSchwartzSubmodule K := by
  intro x hx
  rw [SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth,
    show g x = 0 from not_not.mp (fun h => hx (hg h)), zero_smul]

theorem sobolevCutoffCLM_schwartz_mem_supported (g f : 𝓢(E, ℂ)) {K : Set E}
    (hg : Function.support (g : E → ℂ) ⊆ K) :
    SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g (SobolevIs.CM.Construction.schwartzSobolevCoordinate (1 : ℝ) f) ∈ SobolevIs.CM.Construction.supportedH1Coordinates K := by
  have heq := sobolevCutoffCLM_schwartz 1 g f
  norm_num only [Nat.cast_one] at heq
  rw [heq]
  exact ((SobolevIs.CM.Construction.supportedSchwartzSubmodule K).map (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1)).le_topologicalClosure
    ⟨SchwartzMap.smulLeftCLM ℂ g f,
    schwartz_cutoff_mem_supported g f hg, rfl⟩

theorem sobolevCutoffCLM_supported_preimage_closed (g : 𝓢(E, ℂ)) (K : Set E) :
    IsClosed {u : Lp ℂ 2 (volume : Measure E) | SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u ∈ SobolevIs.CM.Construction.supportedH1Coordinates K} :=
  (((SobolevIs.CM.Construction.supportedSchwartzSubmodule K).map (SobolevIs.CM.Construction.schwartzSobolevCoordinate 1)).isClosed_topologicalClosure).preimage
    (SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g).continuous

/-- A cutoff supported in K sends every genuine H1 function into the
completion of smooth functions supported in K. -/
theorem sobolevCutoffCLM_mem_supported (g : 𝓢(E, ℂ)) {K : Set E}
    (hg : Function.support (g : E → ℂ) ⊆ K) (u : Lp ℂ 2 (volume : Measure E)) :
    SobolevCutoffOperator.CM.Construction.sobolevCutoffCLM 1 g u ∈ SobolevIs.CM.Construction.supportedH1Coordinates K := by
  exact (schwartzSobolevCoordinate_denseRange (E := E) 1).induction_on u
    (sobolevCutoffCLM_supported_preimage_closed g K)
    (fun f => sobolevCutoffCLM_schwartz_mem_supported g f hg)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevSmoothDensity.CM.Construction
