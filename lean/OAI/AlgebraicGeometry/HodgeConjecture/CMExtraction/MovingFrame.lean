import OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity
import OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame

/-! # Moving Frame -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MovingFrame

noncomputable section

/-! Period and determinant transformation for two different frames in
the same rational symplectic coordinates. -/

open _root_.Matrix
open scoped Classical _root_.Matrix

variable {Place : Type*} [Fintype Place] [DecidableEq Place]

theorem moving_frame_block_equations
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z z' : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (t : Module.End ℂ (Geometry.ComplexBall.PrescribedSignsB.Ambient Place)) (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) ℝ)
    (T : Matrix (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) ℂ)
    (hf : ∀ u, t (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame B μ d z u) = RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame B μ d z' (T *ᵥ u))
    (he : ∀ u, e (t u) = Matrix.fromBlocks g.complexify.A g.complexify.B
      g.complexify.C g.complexify.D *ᵥ e u) :
    g.complexify.A * RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame e B μ d z + g.complexify.B * RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame e B μ d z =
        RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame e B μ d z' * T ∧
    g.complexify.C * RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame e B μ d z + g.complexify.D * RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame e B μ d z =
        RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame e B μ d z' * T := by
  have h (u : RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place → ℂ) := he (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame B μ d z u)
  simp only [hf, Matrix.fromBlocks_mulVec] at h
  constructor <;> apply Matrix.ext_iff_mulVec.mpr <;> intro u
  · simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame_mulVec,
      RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (congrArg (fun w => fun i => w (Sum.inl i)) (h u)).symm
  · simpa only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame_mulVec,
      RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame_mulVec, Function.comp_def, Sum.elim_inl, Sum.elim_inr] using
      (congrArg (fun w => fun i => w (Sum.inr i)) (h u)).symm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem moving_frame_period
    (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z Z' : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q Q' T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0)
    (hupper : (g.complexify.A * Z.matrix + g.complexify.B) * Q = Z'.matrix * Q' * T)
    (hlower : g.complexify.denominator Z.matrix * Q = Q' * T) :
    g.transformSiegel Z = Z' := by
  have hQi := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have h := congrArg (fun M : Matrix ι ι ℂ => M * Q⁻¹) hupper
  have hk : Q' * T * Q⁻¹ = g.complexify.denominator Z.matrix := by
    rw [← hlower, Matrix.mul_assoc, hQi, Matrix.mul_one]
  have htop : g.complexify.A * Z.matrix + g.complexify.B =
      Z'.matrix * g.complexify.denominator Z.matrix := by
    rw [Matrix.mul_assoc _ Q Q⁻¹, hQi, Matrix.mul_one] at h
    calc
      _ = Z'.matrix * Q' * T * Q⁻¹ := h
      _ = Z'.matrix * (Q' * T * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hk]
  apply RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization.siegel_matrix_ext
  change (g.complexify.A * Z.matrix + g.complexify.B) *
    (g.complexify.denominator Z.matrix)⁻¹ = Z'.matrix
  rw [htop, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (g.denominator_det_isUnit Z), Matrix.mul_one]

theorem moving_frame_determinant
    (g : ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q Q' T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0)
    (hlower : g.complexify.denominator Z.matrix * Q = Q' * T) :
    (g.complexify.denominator Z.matrix).det = Q'.det * T.det / Q.det := by
  apply (eq_div_iff hQ).mpr
  simpa only [Matrix.det_mul] using congrArg Matrix.det hlower

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.MovingFrame
