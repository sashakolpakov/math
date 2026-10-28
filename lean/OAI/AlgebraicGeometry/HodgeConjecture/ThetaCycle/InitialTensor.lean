import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Slots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.BlockPeriod
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicAnalysis

/-! # Initial Tensor -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialTensor.CM

noncomputable section

/-! One fixed total finite Schwartz input gives the original nonzero
projected second theta derivative. The tensor and projection are literal
Jacobi Hessians and ThetaKernel's double alternation. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [NumberField.IsCMField K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d₀ d₁ : Gal(K/ℚ) → Bool}

def splitThetaSlot (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (a : Fin 2 × Fin 2) :
    Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places) → ℂ :=
  if a.2 = 0 then Sum.elim (Slots.CM.thetaJacobiSlot K L₀ z a.1) 0
  else Sum.elim 0 (Slots.CM.thetaJacobiSlot K L₁ z a.1)

def splitThetaTensor (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)))
    (z : HeckeCycles.GeometricSource.CM.BallChart) : RepresentationTheory.Theta.Kernel.Calculus.TensorCoordinates := fun a b =>
  ((L₀.halfDet z : ℂ) * (L₁.halfDet z : ℂ)) *
    iteratedFDeriv ℂ 2
      (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed Φ (BlockPeriod.CM.blockPeriod (L₀.period z) (L₁.period z))) 0
      ![splitThetaSlot K L₀ L₁ z a, splitThetaSlot K L₀ L₁ z b]

def splitThetaTopCoefficient
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)))
    (z : HeckeCycles.GeometricSource.CM.BallChart) : ℂ := RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (splitThetaTensor K L₀ L₁ Φ z)

theorem split_theta_tensor_factorization
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (φ ψ : HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K places)) (z : HeckeCycles.GeometricSource.CM.BallChart) :
    splitThetaTopCoefficient K L₀ L₁ (RepresentationTheory.Theta.Factorization.Derivative.tensorInput φ ψ) z =
      Slots.CM.sourceWedgeCoefficient K L₀ L₁ φ ψ z := by
  let Z := BlockPeriod.CM.blockPeriod (L₀.period z) (L₁.period z)
  have hm (u v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :=
    RepresentationTheory.Theta.Kernel.Factorization.mixed_completed (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) (IntrinsicAnalysis.CM.nativeDerivativeFactorizationInput _ _)
      (L₀.period z) (L₁.period z) Z rfl (RepresentationTheory.Theta.Factorization.Derivative.tensorInput φ ψ) φ ψ
      (RepresentationTheory.Theta.Factorization.Derivative.tensorInput_apply φ ψ) u v
  have hr (u v : HeckeCycles.GeometricSource.CM.Positions K places → ℂ) :=
    RepresentationTheory.Theta.Kernel.Factorization.mixed_completed_reverse (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) (IntrinsicAnalysis.CM.nativeGaussianConvergenceInput _) (IntrinsicAnalysis.CM.nativeDerivativeFactorizationInput _ _)
      (L₀.period z) (L₁.period z) Z rfl (RepresentationTheory.Theta.Factorization.Derivative.tensorInput φ ψ) φ ψ
      (RepresentationTheory.Theta.Factorization.Derivative.tensorInput_apply φ ψ) u v
  simp only [IntrinsicAnalysis.CM.c38_completed_eq] at hm hr
  change RepresentationTheory.Theta.Kernel.Calculus.doubleAlt (fun a b => ((L₀.halfDet z : ℂ) * (L₁.halfDet z : ℂ)) *
    iteratedFDeriv ℂ 2 (RepresentationTheory.Theta.DerivativeFactorizationDefinitions.completed (RepresentationTheory.Theta.Factorization.Derivative.tensorInput φ ψ) Z) 0
      ![splitThetaSlot K L₀ L₁ z a, splitThetaSlot K L₀ L₁ z b]) = _
  simp only [RepresentationTheory.Theta.Kernel.Calculus.doubleAlt, splitThetaSlot, Fin.isValue, ite_true, one_ne_zero, ite_false,
    hm, hr, Slots.CM.sourceWedgeCoefficient, RepresentationTheory.Theta.Kernel.Calculus.wedgeCoefficient, Slots.CM.source_coordinates_completed_slots]
  ring

theorem exists_initial_total_theta_nonzero [IsGalois ℚ K]
    (L₀ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₀) (L₁ : HeckeCycles.GeometricSource.CM.LinePeriod K B places d₁)
    (z : HeckeCycles.GeometricSource.CM.BallChart) (hz : z ∈ B.domain) :
    ∃ Φ : HeckeCycles.GeometricSource.CM.FiniteInput (Sum (HeckeCycles.GeometricSource.CM.Positions K places) (HeckeCycles.GeometricSource.CM.Positions K places)),
      splitThetaTopCoefficient K L₀ L₁ Φ z ≠ 0 := by
  obtain ⟨φ, ψ, h⟩ := Slots.CM.exists_source_wedge_nonzero K L₀ L₁ z hz
  exact ⟨RepresentationTheory.Theta.Factorization.Derivative.tensorInput φ ψ, by rw [split_theta_tensor_factorization]; exact h⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.InitialTensor.CM
