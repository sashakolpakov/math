import OAI.RepresentationTheory.Hecke.RadialDilation.Archimedean
import OAI.RepresentationTheory.Hecke.RadialDilation.ThetaFirst

/-! # Siegel Frame -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization

noncomputable section

/-!
# Converting period-frame equivariance into determinant and gradient covariance

A period frame in symplectic coordinates has columns (Z Q, Q), with Q
invertible. The two block equations below express the action on those actual
columns. They give a fixed period and identify the denominator with the action
on the period frame by conjugation. No determinant or gradient character is
assumed in these linear algebra lemmas.
-/

open scoped Classical _root_.Matrix
open _root_.Matrix

universe ui ur uf ua
variable {ι : Type ui} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem siegel_matrix_ext {Z Z' : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι} (h : Z.matrix = Z'.matrix) : Z = Z' := by
  cases Z
  cases Z'
  cases h
  rfl

theorem equivariant_frame_fixed_period
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0)
    (hupper : (g.complexify.A * Z.matrix + g.complexify.B) * Q = Z.matrix * Q * T)
    (hlower : g.complexify.denominator Z.matrix * Q = Q * T) :
    g.transformSiegel Z = Z := by
  have hQi := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have h := congrArg (fun M : Matrix ι ι ℂ => M * Q⁻¹) hupper
  have hk : Q * T * Q⁻¹ = g.complexify.denominator Z.matrix := by
    rw [← hlower, Matrix.mul_assoc, hQi, Matrix.mul_one]
  have htop : g.complexify.A * Z.matrix + g.complexify.B =
      Z.matrix * g.complexify.denominator Z.matrix := by
    rw [Matrix.mul_assoc _ Q Q⁻¹, hQi, Matrix.mul_one] at h
    calc
      _ = Z.matrix * Q * T * Q⁻¹ := h
      _ = Z.matrix * (Q * T * Q⁻¹) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hk]
  apply siegel_matrix_ext
  change (g.complexify.A * Z.matrix + g.complexify.B) *
    (g.complexify.denominator Z.matrix)⁻¹ = Z.matrix
  rw [htop, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (g.denominator_det_isUnit Z), Matrix.mul_one]

theorem equivariant_frame_determinant
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0)
    (hlower : g.complexify.denominator Z.matrix * Q = Q * T) :
    (g.complexify.denominator Z.matrix).det = T.det := by
  have h := congrArg Matrix.det hlower
  simp only [Matrix.det_mul] at h
  exact mul_right_cancel₀ hQ (by simpa only [mul_comm Q.det] using h)

def gradientVector (l : (ι → ℂ) →L[ℂ] ℂ) : ι → ℂ :=
  fun i => l (Pi.single i 1)

theorem cotangent_expansion (l : (ι → ℂ) →L[ℂ] ℂ) (v : ι → ℂ) :
    l v = ∑ i, v i * gradientVector l i := by
  have he : v = ∑ i, v i • Pi.single i (1 : ℂ) := by
    ext i
    simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp only [map_sum, map_smul, smul_eq_mul, gradientVector]

theorem gradient_precompose (l : (ι → ℂ) →L[ℂ] ℂ) (M : Matrix ι ι ℂ) :
    gradientVector (l.comp M.mulVecLin.toContinuousLinearMap) =
      M.transpose *ᵥ gradientVector l := by
  funext i
  change l (M *ᵥ Pi.single i 1) = _
  rw [cotangent_expansion]
  simp [Matrix.mulVec, dotProduct, gradientVector, Pi.single_apply]

theorem gradient_of_covariance
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι)
    (lnew l : (ι → ℂ) →L[ℂ] ℂ) (c : ℂ)
    (hc : lnew.comp (g.jacobiChange Z) = c • l) :
    gradientVector lnew = c • (g.complexify.denominator Z.matrix *ᵥ gradientVector l) := by
  have he := congrArg gradientVector hc
  change gradientVector (lnew.comp
    ((g.complexify.denominator Z.matrix)⁻¹ᵀ).mulVecLin.toContinuousLinearMap) = _ at he
  rw [gradient_precompose, Matrix.transpose_transpose] at he
  have he' := congrArg (fun v => g.complexify.denominator Z.matrix *ᵥ v) he
  rw [Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (g.denominator_det_isUnit Z), Matrix.one_mulVec] at he'
  have hs : gradientVector (c • l) = c • gradientVector l := rfl
  rw [hs, Matrix.mulVec_smul] at he'
  exact he'

def frameGradient (Q : Matrix ι ι ℂ) (l : (ι → ℂ) →L[ℂ] ℂ) : ι → ℂ :=
  Q⁻¹ *ᵥ gradientVector l

theorem frameGradient_of_covariance
    (g : AlgebraicGeometry.ComplexMultiplication.CMSymplecticSiegel.CM.SymplecticBlocks ι ℝ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0)
    (hlower : g.complexify.denominator Z.matrix * Q = Q * T)
    (lnew l : (ι → ℂ) →L[ℂ] ℂ) (c : ℂ)
    (hc : lnew.comp (g.jacobiChange Z) = c • l) :
    frameGradient Q lnew = c • (T *ᵥ frameGradient Q l) := by
  have hQi := Matrix.mul_nonsing_inv Q (isUnit_iff_ne_zero.mpr hQ)
  have hiQ := Matrix.nonsing_inv_mul Q (isUnit_iff_ne_zero.mpr hQ)
  have hconj := congrArg (fun M : Matrix ι ι ℂ => Q⁻¹ * M * Q⁻¹) hlower
  have he : Q⁻¹ * g.complexify.denominator Z.matrix = T * Q⁻¹ := by
    simp only [← Matrix.mul_assoc] at hconj
    rw [hiQ, Matrix.one_mul,
      Matrix.mul_assoc (Q⁻¹ * g.complexify.denominator Z.matrix) Q Q⁻¹,
      hQi, Matrix.mul_one] at hconj
    exact hconj
  simp only [frameGradient, gradient_of_covariance g Z lnew l c hc, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, he]

variable {MpR : Type ur} {MpF : Type uf} {MpA : Type ua}
  [Group MpR] [Group MpF] [Group MpA]

/-- PoissonAutomorphy's actual finite-adelic theta derivative in a fixed period frame. -/
theorem actual_frame_theta_covariance
    (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition.{ui, ur, uf, ua})
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData ι MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix ι) (Q T : Matrix ι ι ℂ)
    (hQ : Q.det ≠ 0)
    (hupper : ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A * Z.matrix + (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B) * Q =
      Z.matrix * Q * T)
    (hlower : (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix * Q = Q * T)
    (Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz ι) :
    frameGradient Q (Theta.Geometric.LinearTheta.canonicalFirst (D.finiteAction γ Φ) Z) =
      Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z • (T *ᵥ frameGradient Q (Theta.Geometric.LinearTheta.canonicalFirst Φ Z)) := by
  have hc := ThetaFirst.Realization.actual_first_theta_covariance hPoissonAutomorphy D γ Φ Z
  rw [equivariant_frame_fixed_period (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z Q T hQ hupper hlower] at hc
  exact frameGradient_of_covariance (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z Q T hQ hlower _ _ _ hc

end

end OAI.RepresentationTheory.Hecke.RadialDilation.SiegelFrame.Realization
