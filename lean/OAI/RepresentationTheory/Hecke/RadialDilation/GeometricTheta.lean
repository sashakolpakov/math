import OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity
import OAI.RepresentationTheory.Hecke.RadialDilation.RealStructure

/-! # Geometric Theta -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.GeometricTheta.Realization

noncomputable section

/-! The determinant and first-theta characters of the constructed period. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

universe up ur uf ua
variable {Place : Type up} [Fintype Place]

theorem gradientVector_add {ι : Type*} [Fintype ι] [DecidableEq ι]
    (l m : (ι → ℂ) →L[ℂ] ℂ) : SiegelFrame.Realization.gradientVector (l + m) = SiegelFrame.Realization.gradientVector l + SiegelFrame.Realization.gradientVector m := rfl

theorem gradientVector_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℂ) (l : (ι → ℂ) →L[ℂ] ℂ) : SiegelFrame.Realization.gradientVector (c • l) = c • SiegelFrame.Realization.gradientVector l := rfl

def projectedFrameTheta (μ : Place) (Q : Matrix (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place)) :
    Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex Place) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun Φ i := SiegelFrame.Realization.frameGradient Q (Theta.Geometric.LinearTheta.firstThetaLinear Z Φ) (μ, i.succ)
  map_add' Φ Ψ := by
    ext i
    simp only [map_add, SiegelFrame.Realization.frameGradient, gradientVector_add, Matrix.mulVec_add, Pi.add_apply]
  map_smul' c Φ := by
    ext i
    simp only [map_smul, SiegelFrame.Realization.frameGradient, gradientVector_smul, Matrix.mulVec_smul,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply]

variable {MpR : Type ur} {MpF : Type uf} {MpA : Type ua}
  [Group MpR] [Group MpF] [Group MpA]

theorem projectedFrameTheta_covariance
    (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition.{up, ur, uf, ua})
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ)
    (μ : Place) (d : Place → Bool) (a : Place → ℂ)
    (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place))
    (Q : Matrix (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) ℂ) (hQ : Q.det ≠ 0)
    (hupper : ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A * Z.matrix + (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B) * Q =
      Z.matrix * Q * Archimedean.Realization.periodScalarMatrix μ d a)
    (hlower : (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix * Q =
      Q * Archimedean.Realization.periodScalarMatrix μ d a)
    (Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex Place)) :
    projectedFrameTheta μ Q Z (D.finiteAction γ Φ) =
      (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z * (a μ)⁻¹) • projectedFrameTheta μ Q Z Φ := by
  have h := SiegelFrame.Realization.actual_frame_theta_covariance hPoissonAutomorphy D γ Z Q (Archimedean.Realization.periodScalarMatrix μ d a)
    hQ hupper hlower Φ
  ext i
  have hi := congrFun h (μ, i.succ)
  simpa [projectedFrameTheta, Theta.Geometric.LinearTheta.firstThetaLinear, Archimedean.Realization.periodScalarMatrix, Matrix.mulVec_diagonal,
    Archimedean.Realization.periodWeight, mul_assoc] using hi

theorem positive_matrix_theta_characters
    (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition.{up, ur, uf, ua})
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ)
    (μ : Place) (d : Place → Bool) (a : Place → ℂ) (ha : a μ ≠ 0)
    (P Q : Matrix (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) ℂ)
    (hiso : P.transpose * Q = Q.transpose * P)
    (hpos : ∀ v : FramePositivity.Realization.FrameIndex Place → ℂ, v ≠ 0 →
      0 < (PositiveGraph.Realization.standardFramePairing (P *ᵥ v) (Q *ᵥ v)).im)
    (hup : (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A * P + (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B * Q =
      P * Archimedean.Realization.periodScalarMatrix μ d a)
    (hlo : (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.C * P + (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.D * Q =
      Q * Archimedean.Realization.periodScalarMatrix μ d a) :
    ∃ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place), Z.matrix * Q = P ∧
      Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z ^ 2 = (a μ)⁻¹ *
        ∏ τ ∈ Finset.univ.erase μ, a τ ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
      ∀ Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex Place),
        projectedFrameTheta μ Q Z (D.finiteAction γ Φ) =
          (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z * (a μ)⁻¹) • projectedFrameTheta μ Q Z Φ := by
  let T := Archimedean.Realization.periodScalarMatrix μ d a
  let Z := PositiveGraph.Realization.siegelOfPositiveFrame P Q hiso hpos
  have hZ : Z.matrix * Q = P := PositiveGraph.Realization.siegelOfPositiveFrame_columns P Q hiso hpos
  have hQ := PositiveGraph.Realization.positive_frame_lower_det P Q hpos
  have hupper : ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.A * Z.matrix + (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.B) * Q =
      Z.matrix * Q * T := by
    rw [Matrix.add_mul, Matrix.mul_assoc, hZ]
    exact hup
  have hlower : (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.denominator Z.matrix * Q = Q * T := by
    change ((Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.C * Z.matrix + (Theta.PoissonAutomorphyNormalizationData.realBlocks γ).complexify.D) * Q = Q * T
    rw [Matrix.add_mul, Matrix.mul_assoc, hZ]
    exact hlo
  refine ⟨Z, hZ, ?_, ?_⟩
  · rw [Theta.PoissonAutomorphyNormalizationData.halfDet_sq, SiegelFrame.Realization.equivariant_frame_determinant (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z Q T hQ hlower]
    exact Archimedean.Realization.periodScalarMatrix_det μ d a ha
  · exact projectedFrameTheta_covariance hPoissonAutomorphy D γ μ d a Z Q hQ hupper hlower

/-- Both RadialDilation characters are derived from the concrete rational scalar and
the positive period frame. The half determinant and theta map are PoissonAutomorphy's and
GeometricTheta's actual constructions. -/
theorem rational_period_theta_characters
    (hPoissonAutomorphy : Prerequisites.Core.PoissonAutomorphy.Proposition.{up, ur, uf, ua})
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ)
    (hr : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (σ : Place → E →ₐ[ℚ] ℂ) (hσ : Function.Bijective (Complexification.Realization.pairingEmbeddings σ))
    (e : (Fin 3 → E) ≃ₗ[ℚ] (Sum (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) → ℚ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart)
    (ψ : Geometry.ComplexBall.PrescribedSignsB.Ambient Place → Geometry.ComplexBall.PrescribedSignsB.Ambient Place → ℂ)
    (hpair : ∀ u v, FramePositivity.Realization.coordinatePairing (RationalCoordinates.Realization.rationalCoordinates E σ hσ e u)
      (RationalCoordinates.Realization.rationalCoordinates E σ hσ e v) = ψ u v)
    (hp : Geometry.ComplexBall.PrescribedSignsB.PositivePeriod (3 * Fintype.card Place) ψ Geometry.ComplexBall.PrescribedSignsB.realConj
      (LinearMap.range (Geometry.ComplexBall.PrescribedSignsB.globalFrame B μ d z)))
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ) (hγ : γ.val = RationalCoordinates.Realization.rationalScalarMatrix E e (r : E)) :
    let Q := FramePositivity.Realization.lowerFrame (RationalCoordinates.Realization.rationalCoordinates E σ hσ e) B μ d z
    ∃ Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place),
      Z.matrix * Q = FramePositivity.Realization.upperFrame (RationalCoordinates.Realization.rationalCoordinates E σ hσ e) B μ d z ∧
      Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z ^ 2 = (σ μ (r : E))⁻¹ *
        ∏ τ ∈ Finset.univ.erase μ, σ τ (r : E) ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
      ∀ Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex Place),
        projectedFrameTheta μ Q Z (D.finiteAction γ Φ) =
          (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z * (σ μ (r : E))⁻¹) • projectedFrameTheta μ Q Z Φ := by
  let ec := RationalCoordinates.Realization.rationalCoordinates E σ hσ e
  obtain ⟨hiso, hpos⟩ := FramePositivity.Realization.positivePeriod_frame_matrices ec B μ d z ψ hpair
    (RealStructure.Realization.rationalCoordinates_realConj E σ hσ e) hp
  obtain ⟨hup, hlo⟩ := FramePositivity.Realization.rational_frame_block_equations E r hr σ hσ e B μ d z γ hγ
  have ha : σ μ (r : E) ≠ 0 := (map_ne_zero (σ μ)).mpr (Units.ne_zero r)
  exact positive_matrix_theta_characters hPoissonAutomorphy D γ μ d (fun τ => σ τ (r : E)) ha
    (FramePositivity.Realization.upperFrame ec B μ d z) (FramePositivity.Realization.lowerFrame ec B μ d z) hiso hpos hup hlo

end

end OAI.RepresentationTheory.Hecke.RadialDilation.GeometricTheta.Realization
