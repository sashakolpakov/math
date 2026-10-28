import OAI.RepresentationTheory.Hecke.RadialDilation.GeometricFinite
import OAI.RepresentationTheory.Hecke.RadialDilation.ArchimedeanRealization

/-! # Geometric Specs -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSpecs.Realization

noncomputable section

/-! Compact propositions recording the four concrete analytic inputs of RadialDilation. -/

open scoped Classical _root_.Matrix

variable {Place : Type*} [Fintype Place]
variable {MpR MpF MpA : Type*} [Group MpR] [Group MpF] [Group MpA]

def FiniteRadialRealization (q : ℕ) [Fact q.Prime] (μ : Place)
    (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA) (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ)
    (s : MpF) (Uq : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q) (ξ : ℂ) (M : ℕ) : Prop :=
  Function.Injective (ConcreteFinite.Realization.coordinateRadialEmbedding q μ D s) ∧ Cm.finitePhase ξ ∧
    (∀ (b : Cm.radialInput q) (x : Mem.Realization.Position q), (Uq b).val x =
      (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
        b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)) ∧
    (∀ b : Cm.radialInput q,
      D.finiteAction γ (ConcreteFinite.Realization.coordinateRadialEmbedding q μ D s b) =
        ξ • ConcreteFinite.Realization.coordinateRadialEmbedding q μ D s (Uq b))

def ThetaScalarRealization (D : Theta.PoissonAutomorphyNormalizationData.WeilData (FramePositivity.Realization.FrameIndex Place) MpR MpF MpA)
    (γ : Theta.PoissonAutomorphyNormalizationData.Sp (FramePositivity.Realization.FrameIndex Place) ℚ) (μ : Place) (d : Place → Bool) (a : Place → ℂ)
    (P Q : Matrix (FramePositivity.Realization.FrameIndex Place) (FramePositivity.Realization.FrameIndex Place) ℂ) (Z : AlgebraicGeometry.ComplexMultiplication.CMSiegelMatrix.CM.SiegelMatrix (FramePositivity.Realization.FrameIndex Place)) : Prop :=
  Z.matrix * Q = P ∧
    Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z ^ 2 = (a μ)⁻¹ *
      ∏ τ ∈ Finset.univ.erase μ, a τ ^ (-3 * AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (d τ)) ∧
    ∀ Φ : Theta.PoissonAutomorphyNormalizationData.finiteSchwartz (FramePositivity.Realization.FrameIndex Place),
      GeometricTheta.Realization.projectedFrameTheta μ Q Z (D.finiteAction γ Φ) =
        (Theta.PoissonAutomorphyNormalizationData.halfDet (Theta.PoissonAutomorphyNormalizationData.realBlocks γ) Z * (a μ)⁻¹) • GeometricTheta.Realization.projectedFrameTheta μ Q Z Φ

end

end OAI.RepresentationTheory.Hecke.RadialDilation.GeometricSpecs.Realization
