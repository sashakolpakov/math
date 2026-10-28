import OAI.Analysis.HodgeTheory.Decomposition.SchwartzCoordinates
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds

/-! # Sobolev Postcomposition -/

namespace OAI.Analysis.HodgeTheory.Decomposition.SobolevPostcomposition.Constructions

noncomputable section

/-! Genuine continuous linear coefficient maps commute with distributions
and Bessel potentials and preserve native vector Sobolev regularity. -/

open _root_.MeasureTheory TemperedDistribution
open scoped SchwartzMap

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]

def distributionPostcomposition (L : F →L[ℂ] G) : 𝓢'(E, F) →L[ℂ] 𝓢'(E, G) :=
  PointwiseConvergenceCLM.postcomp 𝓢(E, ℂ) L

theorem distributionPostcomposition_schwartz (L : F →L[ℂ] G) (f : 𝓢(E, F)) :
    distributionPostcomposition L (f : 𝓢'(E, F)) =
      (SchwartzMap.postcompCLM L f : 𝓢'(E, G)) := by
  ext φ
  change L (∫ x, φ x • f x) = ∫ x, φ x • L (f x)
  have hi : Integrable (fun x => φ x • f x) (volume : Measure E) := by
    apply (SchwartzMap.smulLeftCLM F φ f).integrable.congr
    exact Filter.Eventually.of_forall (fun x =>
      SchwartzMap.smulLeftCLM_apply_apply φ.hasTemperateGrowth f x)
  calc
    _ = ∫ x, L (φ x • f x) := (L.integral_comp_comm hi).symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall (fun x => L.map_smul (φ x) (f x)))

theorem distributionPostcomposition_Lp (L : F →L[ℂ] G) (u : Lp F 2 (volume : Measure E)) :
    distributionPostcomposition L (u : 𝓢'(E, F)) =
      (L.compLpL 2 volume u : 𝓢'(E, G)) := by
  have hdense := SchwartzMap.denseRange_toLpCLM (E := E) (F := F)
    (μ := (volume : Measure E)) (p := 2) (by norm_num)
  have hclosed : IsClosed {v : Lp F 2 (volume : Measure E) |
      distributionPostcomposition L (v : 𝓢'(E, F)) = (L.compLpL 2 volume v : 𝓢'(E, G))} :=
    isClosed_eq ((distributionPostcomposition L).continuous.comp
      (Lp.toTemperedDistributionCLM F volume 2).continuous)
      ((Lp.toTemperedDistributionCLM G volume 2).continuous.comp (L.compLpL 2 volume).continuous)
  refine hdense.induction_on u hclosed (fun f => ?_)
  change distributionPostcomposition L (f.toLp 2 volume : 𝓢'(E, F)) =
    (L.compLpL 2 volume (f.toLp 2 volume) : 𝓢'(E, G))
  have hp : L.compLpL 2 volume (f.toLp 2 volume) = (SchwartzMap.postcompCLM L f).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [L.coeFn_compLpL (f.toLp 2 volume), f.coeFn_toLp 2 volume,
      (SchwartzMap.postcompCLM L f).coeFn_toLp 2 volume] with x hL hf hg
    exact hL.trans ((congrArg L hf).trans hg.symm)
  rw [hp, Lp.toTemperedDistribution_toLp_eq, Lp.toTemperedDistribution_toLp_eq]
  exact distributionPostcomposition_schwartz L f

omit [CompleteSpace F] [CompleteSpace G] in
theorem distributionPostcomposition_bessel (L : F →L[ℂ] G) (s : ℝ) (u : 𝓢'(E, F)) :
    distributionPostcomposition L (besselPotential E F s u) =
      besselPotential E G s (distributionPostcomposition L u) := by
  ext φ
  rfl

theorem memSobolev_postcomposition (L : F →L[ℂ] G) {s : ℝ} {u : 𝓢'(E, F)}
    (hu : MemSobolev s 2 u) : MemSobolev s 2 (distributionPostcomposition L u) := by
  obtain ⟨f, hf⟩ := hu
  refine ⟨L.compLpL 2 volume f, ?_⟩
  rw [← distributionPostcomposition_bessel, hf, distributionPostcomposition_Lp]

end

end OAI.Analysis.HodgeTheory.Decomposition.SobolevPostcomposition.Constructions
