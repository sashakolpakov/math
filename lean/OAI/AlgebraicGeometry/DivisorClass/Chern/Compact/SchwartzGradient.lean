import OAI.AlgebraicGeometry.DivisorClass.Chern.VectorGradientNormalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.Adjoint

/-! # Schwartz Gradient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SchwartzGradient

noncomputable section

/-! The normalized gradient of a compact Schwartz test is itself an actual compact Schwartz function. -/

open _root_.MeasureTheory
open scoped ContDiff SchwartzMap

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℂ F]

def testDerivativeCoordinates (b : OrthonormalBasis ι ℝ E) :
    (E →L[ℝ] F) →L[ℝ] PiLp 2 (fun _ : ι => F) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ContinuousLinearMap.apply ℝ F (b i)))

def schwartzNormalizedGradientField (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F)) (z : E) :
    PiLp 2 (fun _ : ι => F) :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • testDerivativeCoordinates b (fderiv ℝ q z)

theorem schwartzNormalizedGradientField_smooth (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F)) :
    ContDiff ℝ ∞ (schwartzNormalizedGradientField b q) :=
  ((testDerivativeCoordinates b).contDiff.comp ((q.smooth ⊤).fderiv_right (by simp))).const_smul _

theorem schwartzNormalizedGradientField_tsupport (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F)) :
    tsupport (schwartzNormalizedGradientField b q) ⊆ tsupport q :=
  (tsupport_comp_subset (g := fun L : E →L[ℝ] F =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • testDerivativeCoordinates b L) (by simp) (fderiv ℝ q)).trans
      (tsupport_fderiv_subset ℝ)

theorem schwartzNormalizedGradientField_compact (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F))
    (hq : HasCompactSupport q) : HasCompactSupport (schwartzNormalizedGradientField b q) :=
  hq.of_isClosed_subset (isClosed_tsupport _) (schwartzNormalizedGradientField_tsupport b q)

def compactSchwartzGradient (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F)) (hq : HasCompactSupport q) :
    𝓢(E, PiLp 2 (fun _ : ι => F)) :=
  (schwartzNormalizedGradientField_compact b q hq).toSchwartzMap
    (schwartzNormalizedGradientField_smooth b q)

theorem compactSchwartzGradient_apply (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F))
    (hq : HasCompactSupport q) (z : E) : compactSchwartzGradient b q hq z =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • WithLp.toLp 2 (fun i => fderiv ℝ q z (b i)) := rfl

theorem compactSchwartzGradient_tsupport (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F))
    (hq : HasCompactSupport q) : tsupport (compactSchwartzGradient b q hq) ⊆ tsupport q :=
  schwartzNormalizedGradientField_tsupport b q

theorem compactSchwartzGradient_compact (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F))
    (hq : HasCompactSupport q) : HasCompactSupport (compactSchwartzGradient b q hq) :=
  hq.of_isClosed_subset (isClosed_tsupport _) (compactSchwartzGradient_tsupport b q hq)

theorem compactSchwartzGradient_toLp [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace F] (b : OrthonormalBasis ι ℝ E) (q : 𝓢(E, F)) (hq : HasCompactSupport q) :
    (compactSchwartzGradient b q hq).toLp 2 volume = Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := F) b (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) := by
  apply Lp.ext
  apply Filter.Eventually.mono (((compactSchwartzGradient b q hq).coeFn_toLp 2 volume).and
    (VectorGradientNormalization.vectorGradient_physical_schwartz b q))
  intro z hz
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hgrad := congrArg (fun v : PiLp 2 (fun _ : ι => F) => (2 * Real.pi * Complex.I : ℂ)⁻¹ • v) hz.2
  have hcancel := inv_smul_smul₀ hκ (Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := F) b (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSchwartzSobolevCoordinate 1 q) z)
  exact hz.1.trans ((compactSchwartzGradient_apply b q hq z).trans (hgrad.symm.trans hcancel))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SchwartzGradient
