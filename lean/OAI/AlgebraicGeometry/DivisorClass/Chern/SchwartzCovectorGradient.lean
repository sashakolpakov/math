import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorField
import OAI.AlgebraicGeometry.DivisorClass.Chern.Compact.SchwartzGradient

/-! # Schwartz Covector Gradient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorGradient

noncomputable section

/-! Pointwise physical normalization of the compact Schwartz covector test gradient. -/

open scoped SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem compactSchwartzGradient_covector {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Fintype ι] [LinearOrder ι]
    (b : OrthonormalBasis ι ℝ E) (n : ℕ) (q : 𝓢(E, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates ι n)) (hq : HasCompactSupport q) (z : E) :
    (2 * Real.pi * Complex.I : ℂ) • Compact.SchwartzGradient.compactSchwartzGradient b q hq z =
      TensorGradientCoordinates.covectorTensorGradientCoordinates b.toBasis n (fderiv ℝ (SchwartzCovectorField.schwartzCovectorField b.toBasis n q) z) := by
  have hκ : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hphys := (congrArg (fun v : GradientTensorCoordinates.CovectorGradientCoordinates ι n => (2 * Real.pi * Complex.I : ℂ) • v)
    (Compact.SchwartzGradient.compactSchwartzGradient_apply b q hq z)).trans
      (smul_inv_smul₀ hκ (WithLp.toLp 2 (fun j => fderiv ℝ q z (b j))))
  exact hphys.trans (PiLp.ext (fun j => SchwartzCovectorField.schwartzCovectorField_derivative b.toBasis n q z (b j)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorGradient
