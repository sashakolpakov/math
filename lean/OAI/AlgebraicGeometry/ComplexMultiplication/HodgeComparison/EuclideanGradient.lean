import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceProduct
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GradientSupport

/-! # Euclidean Gradient -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient.CM.Construction

noncomputable section

/-! Genuine Euclidean H1 gradients as vector-valued L2 functions, with their
graph norm and commutation with spatial difference quotients. -/

open _root_.MeasureTheory

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι]

def sobolevVectorGradient (b : OrthonormalBasis ι ℝ E) :
    Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp (EuclideanSpace ℂ ι) 2 (volume : Measure E) :=
  (LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ)).comp (FourierEnergy.CM.Construction.sobolevNormalizedGradient b)

theorem sobolevVectorGradient_norm (b : OrthonormalBasis ι ℝ E) (u : Lp ℂ 2 (volume : Measure E)) :
    ‖sobolevVectorGradient b u‖ = ‖FourierEnergy.CM.Construction.sobolevNormalizedGradient b u‖ :=
  (LpComponents.CM.Construction.lpOrthonormalSynthesisIsometry (EuclideanSpace.basisFun ι ℂ)).norm_map _

theorem sobolevVectorGradient_graph_norm (b : OrthonormalBasis ι ℝ E) (u : Lp ℂ 2 (volume : Measure E)) :
    ‖u‖ ^ 2 = ‖SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ ^ 2 + ‖sobolevVectorGradient b u‖ ^ 2 := by
  have h := congrArg (RCLike.re (K := ℂ)) (FourierEnergy.CM.Construction.sobolev_graph_inner b u u)
  simp only [map_add] at h
  rw [← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner, ← norm_sq_eq_re_inner] at h
  rw [sobolevVectorGradient_norm]
  exact h

theorem sobolevVectorGradient_graph_bound (b : OrthonormalBasis ι ℝ E) (u : Lp ℂ 2 (volume : Measure E)) :
    ‖u‖ ≤ ‖SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u‖ + ‖sobolevVectorGradient b u‖ := by
  have h := sobolevVectorGradient_graph_norm b u
  have hu := norm_nonneg u
  have hJ := norm_nonneg (SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) u)
  have hD := norm_nonneg (sobolevVectorGradient b u)
  nlinarith [mul_nonneg hJ hD]

theorem sobolevVectorGradient_translation (b : OrthonormalBasis ι ℝ E)
    (m : E) (u : Lp ℂ 2 (volume : Measure E)) :
    sobolevVectorGradient b (Translations.CM.Construction.l2Translation m u) = DifferenceProduct.CM.Construction.realL2Translation m (sobolevVectorGradient b u) := by
  have hcomponent (i : ι) : FourierEnergy.CM.Construction.sobolevNormalizedGradient b (Translations.CM.Construction.l2Translation m u) i =
      Translations.CM.Construction.l2Translation m (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i) :=
    (DifferenceBounds.CM.Construction.l2Translation_multiplier_comm m (FourierEnergy.CM.Construction.sobolevEnergySymbol_temperate b (some i))
      (FourierEnergy.CM.Construction.sobolevEnergySymbol_bound b (some i)) u).symm
  have hcomponent_ae : ∀ᵐ x ∂(volume : Measure E), ∀ i,
      (FourierEnergy.CM.Construction.sobolevNormalizedGradient b (Translations.CM.Construction.l2Translation m u) i) x = (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i) (x + m) := by
    apply ae_all_iff.mpr
    intro i
    rw [hcomponent]
    exact Translations.CM.Construction.l2Translation_coe m (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u i)
  apply Lp.ext
  filter_upwards [LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ)
      (FourierEnergy.CM.Construction.sobolevNormalizedGradient b (Translations.CM.Construction.l2Translation m u)),
    (measurePreserving_add_right volume m).quasiMeasurePreserving.ae
      (LpComponents.CM.Construction.lpOrthonormalSynthesis_coe (EuclideanSpace.basisFun ι ℂ) (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u)),
    hcomponent_ae, DifferenceProduct.CM.Construction.realL2Translation_coe m (sobolevVectorGradient b u)] with x hleft hright hcomp htrans
  change LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) (FourierEnergy.CM.Construction.sobolevNormalizedGradient b (Translations.CM.Construction.l2Translation m u)) x = _
  rw [hleft, htrans]
  change _ = LpComponents.CM.Construction.lpOrthonormalSynthesis (EuclideanSpace.basisFun ι ℂ) (FourierEnergy.CM.Construction.sobolevNormalizedGradient b u) (x + m)
  rw [hright]
  simp only [hcomp]

theorem sobolevVectorGradient_difference (b : OrthonormalBasis ι ℝ E)
    (m : E) (t : ℝ) (u : Lp ℂ 2 (volume : Measure E)) :
    sobolevVectorGradient b (DifferenceQuotients.CM.Construction.l2DifferenceQuotient m t u) =
      DifferenceProduct.CM.Construction.realL2Difference m t (sobolevVectorGradient b u) := by
  change sobolevVectorGradient b ((t : ℂ)⁻¹ • (Translations.CM.Construction.l2Translation (t • m) u - u)) =
    t⁻¹ • (DifferenceProduct.CM.Construction.realL2Translation (t • m) (sobolevVectorGradient b u) - sobolevVectorGradient b u)
  rw [map_smul, map_sub, sobolevVectorGradient_translation, ← Complex.ofReal_inv, Complex.coe_smul]
  rfl

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EuclideanGradient.CM.Construction
