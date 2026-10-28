import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange

/-! # Vector Sobolev Density -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevDensity.Constructions

noncomputable section

/-! Density of genuine vector-valued Schwartz functions in native Sobolev coordinates. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorSchwartzBesselPotential (s : ℝ) : 𝓢(E, F) →L[ℂ] 𝓢(E, F) :=
  SchwartzMap.fourierMultiplierCLM F (fun x : E => (((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ) : ℂ))

theorem vectorSchwartzBesselPotential_distribution (s : ℝ) (f : 𝓢(E, F)) :
    (vectorSchwartzBesselPotential s f : 𝓢'(E, F)) = besselPotential E F s (f : 𝓢'(E, F)) :=
  (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) f).symm

theorem vectorSchwartzSobolevCoordinate_inverseBessel (s : ℝ) (f : 𝓢(E, F)) :
    VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate s (vectorSchwartzBesselPotential (-s) f) = f.toLp 2 (volume : Measure E) := by
  apply (LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
    (F := F) (μ := (volume : Measure E)) (p := 2)))
  change (((AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv E F s).symm
    ⟨(vectorSchwartzBesselPotential (-s) f : 𝓢'(E, F)), (vectorSchwartzBesselPotential (-s) f).memSobolev⟩) :
      𝓢'(E, F)) = ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, F))
  rw [AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds.CM.Construction.sobolevCoordinateEquiv_symm_distribution]
  change besselPotential E F s (vectorSchwartzBesselPotential (-s) f : 𝓢'(E, F)) =
    ((f.toLp 2 (volume : Measure E)) : 𝓢'(E, F))
  rw [vectorSchwartzBesselPotential_distribution,
    besselPotential_besselPotential_apply, neg_add_cancel, besselPotential_zero,
    ContinuousLinearMap.id_apply, Lp.toTemperedDistribution_toLp_eq]

theorem vectorSchwartzSobolevCoordinate_denseRange (s : ℝ) :
    DenseRange (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate (E := E) (F := F) s) := by
  have hsub : Set.range (SchwartzMap.toLpCLM ℝ F 2 (volume : Measure E)) ⊆
      Set.range (VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate (E := E) (F := F) s) := by
    rintro _ ⟨f, rfl⟩
    exact ⟨vectorSchwartzBesselPotential (-s) f, vectorSchwartzSobolevCoordinate_inverseBessel s f⟩
  intro u
  exact closure_mono hsub ((SchwartzMap.denseRange_toLpCLM (E := E) (F := F)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)) u)

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorSobolevDensity.Constructions
