import OAI.Analysis.HodgeTheory.Decomposition.VectorDifferenceBounds
import OAI.Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange
import OAI.Analysis.HodgeTheory.Decomposition.FiniteLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct

/-! # Vector Gradient -/

namespace OAI.Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions

noncomputable section

/-! Genuine Euclidean H1 gradients as vector-valued L2 functions, with their
graph norm and commutation with spatial difference quotients. -/

open _root_.MeasureTheory

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

def vectorSobolevGradient (b : OrthonormalBasis ι ℝ E) :
    Lp F 2 (volume : Measure E) →L[ℂ] Lp (PiLp 2 (fun _ : ι => F)) 2 (volume : Measure E) :=
  (FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E))).comp (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b)

theorem vectorSobolevGradient_norm (b : OrthonormalBasis ι ℝ E) (u : Lp F 2 (volume : Measure E)) :
    ‖vectorSobolevGradient (F := F) b u‖ = ‖VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u‖ :=
  FiniteLp.Constructions.finiteLpSynthesis_norm (𝕜 := ℂ) _

theorem vectorSobolevGradient_graph_norm (b : OrthonormalBasis ι ℝ E) (u : Lp F 2 (volume : Measure E)) :
    ‖u‖ ^ 2 = ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ ^ 2 + ‖vectorSobolevGradient (F := F) b u‖ ^ 2 := by
  have h := congrArg (RCLike.re (K := ℂ)) (VectorSobolevEnergy.Constructions.vectorSobolev_graph_inner b u u)
  simp only [map_add] at h
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h
  rw [vectorSobolevGradient_norm]
  exact h

theorem vectorSobolevGradient_graph_bound (b : OrthonormalBasis ι ℝ E) (u : Lp F 2 (volume : Measure E)) :
    ‖u‖ ≤ ‖AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ + ‖vectorSobolevGradient (F := F) b u‖ := by
  have h := vectorSobolevGradient_graph_norm b u
  have hu := norm_nonneg u
  have hJ := norm_nonneg (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)
  have hD := norm_nonneg (vectorSobolevGradient (F := F) b u)
  nlinarith [mul_nonneg hJ hD]

variable [InnerProductSpace ℝ F] [IsScalarTower ℝ ℂ F]

omit [IsScalarTower ℝ ℂ F] in
theorem vectorSobolevGradient_translation (b : OrthonormalBasis ι ℝ E)
    (m : E) (u : Lp F 2 (volume : Measure E)) :
    vectorSobolevGradient (F := F) b (VectorTranslations.Constructions.vectorL2Translation m u) = AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Translation m (vectorSobolevGradient (F := F) b u) := by
  have hcomponent (i : ι) : VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorTranslations.Constructions.vectorL2Translation m u) i =
      VectorTranslations.Constructions.vectorL2Translation m (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i) :=
    (VectorDifferenceBounds.Constructions.vectorL2Translation_multiplier_comm m (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_temperate b (some i))
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.FourierEnergy.CM.Construction.sobolevEnergySymbol_bound b (some i)) u).symm
  have hcomponent_ae : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorTranslations.Constructions.vectorL2Translation m u) i) x = (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i) (x + m) := by
    apply ae_all_iff.mpr
    intro i
    rw [hcomponent]
    exact VectorTranslations.Constructions.vectorL2Translation_coe m (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u i)
  apply Lp.ext
  filter_upwards [FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ)
      (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorTranslations.Constructions.vectorL2Translation m u)),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae
      (FiniteLp.Constructions.finiteLpSynthesis_coe (𝕜 := ℂ) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u)),
    hcomponent_ae, AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Translation_coe m (vectorSobolevGradient (F := F) b u)] with x hleft hright hcomp htrans
  change FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b (VectorTranslations.Constructions.vectorL2Translation m u)) x = _
  rw [hleft, htrans]
  change _ = FiniteLp.Constructions.finiteLpSynthesis (𝕜 := ℂ) (F := F) (ι := ι) (μ := (volume : Measure E)) (VectorSobolevEnergy.Constructions.vectorSobolevNormalizedGradient b u) (x + m)
  rw [hright]
  simp only [hcomp]

theorem vectorSobolevGradient_difference (b : OrthonormalBasis ι ℝ E)
    (m : E) (t : ℝ) (u : Lp F 2 (volume : Measure E)) :
    vectorSobolevGradient (F := F) b (VectorDifferences.Constructions.vectorL2DifferenceQuotient m t u) =
      AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Difference m t (vectorSobolevGradient (F := F) b u) := by
  change vectorSobolevGradient (F := F) b ((t : ℂ)⁻¹ • (VectorTranslations.Constructions.vectorL2Translation (t • m) u - u)) =
    t⁻¹ • (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct.CM.Construction.realL2Translation (t • m) (vectorSobolevGradient (F := F) b u) - vectorSobolevGradient (F := F) b u)
  rw [map_smul, map_sub, vectorSobolevGradient_translation, ← Complex.ofReal_inv]
  exact IsScalarTower.algebraMap_smul ℂ t⁻¹ _

end

end OAI.Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions
