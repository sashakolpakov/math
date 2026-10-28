import OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame

/-! # Moving Gradient -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MovingGradient.Frame

noncomputable section

/-! First-theta gradient covariance between distinct period frames. -/

open _root_.Matrix OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization
open scoped _root_.Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem moving_frame_gradient
    (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q Q' T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0) (hQ' : Q'.det ≠ 0)
    (hlower : g.complexify.denominator Z.matrix * Q = Q' * T)
    (lnew l : (ι → ℂ) →L[ℂ] ℂ) (c : ℂ)
    (hc : lnew.comp (g.jacobiChange Z) = c • l) :
    RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient Q' lnew = c • (T *ᵥ RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient Q l) := by
  have hQi := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have hQ'i := Matrix.nonsing_inv_mul Q' (isUnit_iff_ne_zero.mpr hQ')
  have hm : Q'⁻¹ * g.complexify.denominator Z.matrix = T * Q⁻¹ := by
    calc
      _ = Q'⁻¹ * (g.complexify.denominator Z.matrix * Q) * Q⁻¹ := by
        simp only [Matrix.mul_assoc, hQi, Matrix.mul_one]
      _ = Q'⁻¹ * (Q' * T) * Q⁻¹ := by rw [hlower]
      _ = _ := by rw [← Matrix.mul_assoc Q'⁻¹ Q' T, hQ'i, Matrix.one_mul]
  unfold RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.frameGradient
  rw [RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.gradient_of_covariance g Z lnew l c hc, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MovingGradient.Frame
