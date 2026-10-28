import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactKernel
import Mathlib.Analysis.Complex.Exponential

/-! # Compact Fourier -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactFourier.CM.Construction

noncomputable section

/-! Compact Fourier operators between compact spatial and frequency domains. -/

open _root_.MeasureTheory
open scoped BoundedContinuousFunction

variable {E X Y : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [CompactSpace Y]

/-- The genuine exponential Fourier kernel restricted to two compact parameter domains. -/
def compactFourierKernel (position : C(X, E)) (frequency : C(Y, E)) : C(Y, C(X, ℂ)) :=
  (⟨fun p : Y × X => Complex.exp
      ((-2 * Real.pi * inner ℝ (position p.2) (frequency p.1) : ℝ) * Complex.I),
    by fun_prop⟩ : C(Y × X, ℂ)).curry

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The restricted Fourier integral as an operator from L² to continuous functions. -/
def compactFourierMap (position : C(X, E)) (frequency : C(Y, E)) :
    Lp ℂ 2 μ →L[ℂ] (Y →ᵇ ℂ) :=
  CompactKernel.CM.Construction.continuousIntegralKernelMap μ (compactFourierKernel position frequency)

theorem compactFourierMap_apply (position : C(X, E)) (frequency : C(Y, E))
    (f : Lp ℂ 2 μ) (y : Y) :
    compactFourierMap μ position frequency f y =
      ∫ x, Complex.exp ((-2 * Real.pi * inner ℝ (position x) (frequency y) : ℝ) * Complex.I) *
        f x ∂μ := by
  exact CompactKernel.CM.Construction.continuousIntegralKernelMap_apply μ (compactFourierKernel position frequency) f y

/-- Cutting both the spatial domain and frequency domain to compact sets gives a compact operator. -/
theorem compactFourierMap_isCompact (position : C(X, E)) (frequency : C(Y, E)) :
    IsCompactOperator (compactFourierMap μ position frequency) :=
  CompactKernel.CM.Construction.continuousIntegralKernelMap_isCompact μ (compactFourierKernel position frequency)

variable [MeasurableSpace Y] [BorelSpace Y] (ν : Measure Y) [IsFiniteMeasure ν]

/-- The same genuine Fourier integral with its output in L² of the frequency domain. -/
def compactFourierLpMap (position : C(X, E)) (frequency : C(Y, E)) :
    Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 ν :=
  (BoundedContinuousFunction.toLp 2 ν ℂ).comp (compactFourierMap μ position frequency)

theorem compactFourierLpMap_isCompact (position : C(X, E)) (frequency : C(Y, E)) :
    IsCompactOperator (compactFourierLpMap μ ν position frequency) :=
  (compactFourierMap_isCompact μ position frequency).clm_comp
    (BoundedContinuousFunction.toLp 2 ν ℂ)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CompactFourier.CM.Construction
