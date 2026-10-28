import OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity

/-! # Period Frame Families -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFrameFamilies.Multiplicity

noncomputable section

/-! The prescribed PrescribedSigns frames are holomorphic in their ball-chart
variable in the actual rational symplectic coordinates. -/

open OAI.RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization
open scoped Classical _root_.Matrix

variable {Place : Type*} [Fintype Place] [DecidableEq Place]

omit [Fintype Place] in
theorem flatFrame_differentiable (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hq : ∀ z ∈ O, B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0)
    (v : RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place → ℂ) : DifferentiableOn ℂ (fun z => RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame B μ d z v) O := by
  apply differentiableOn_pi.mpr
  intro τ
  change DifferentiableOn ℂ (fun z => Geometry.ComplexBall.PrescribedSignsB.placeFrame B μ d z τ (fun i => v (τ, i))) O
  by_cases hτ : τ = μ
  · subst τ
    simpa only [Geometry.ComplexBall.PrescribedSignsB.placeFrame, ↓reduceIte] using Geometry.ComplexBall.PrescribedSignsB.localFrame_differentiable (B μ) O hq (fun i => v (μ, i))
  · simp only [Geometry.ComplexBall.PrescribedSignsB.placeFrame, ite_eq_right hτ]
    split_ifs <;> exact differentiableOn_const _

theorem upperFrame_differentiable
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hq : ∀ z ∈ O, B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0) :
    DifferentiableOn ℂ (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.upperFrame e B μ d) O := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  change DifferentiableOn ℂ (fun z => e (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame B μ d z (Pi.single j 1)) (Sum.inl i)) O
  let f := (LinearMap.proj (Sum.inl i)).comp e.toLinearMap
  exact f.toContinuousLinearMap.differentiable.comp_differentiableOn
    (flatFrame_differentiable B μ d O hq (Pi.single j 1))

theorem lowerFrame_differentiable
    (e : Geometry.ComplexBall.PrescribedSignsB.Ambient Place ≃ₗ[ℂ] (Sum (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.FrameIndex Place) → ℂ))
    (B : Place → Geometry.ComplexBall.PrescribedSignsB.Bilin) (μ : Place) (d : Place → Bool)
    (O : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hq : ∀ z ∈ O, B μ (Geometry.ComplexBall.PrescribedSignsB.lineVector z) (Geometry.ComplexBall.PrescribedSignsB.axis 2) ≠ 0) :
    DifferentiableOn ℂ (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.lowerFrame e B μ d) O := by
  apply differentiableOn_pi.mpr
  intro i
  apply differentiableOn_pi.mpr
  intro j
  change DifferentiableOn ℂ (fun z => e (RepresentationTheory.Hecke.RadialDilation.FramePositivity.Realization.flatFrame B μ d z (Pi.single j 1)) (Sum.inr i)) O
  let f := (LinearMap.proj (Sum.inr i)).comp e.toLinearMap
  exact f.toContinuousLinearMap.differentiable.comp_differentiableOn
    (flatFrame_differentiable B μ d O hq (Pi.single j 1))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PeriodFrameFamilies.Multiplicity
