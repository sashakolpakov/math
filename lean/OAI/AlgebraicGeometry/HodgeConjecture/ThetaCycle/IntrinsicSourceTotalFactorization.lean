import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumSlots
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceIntrinsicKernelFactorization

/-! # Intrinsic Source Total Factorization -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicSourceTotalFactorization.CM

noncomputable section

/-! The full native ThetaKernel factorization applies to the original source
total finite input, through its proved exact total comparison. The result
is a finite sum of actual source wedge coefficients on the same ball. -/

open scoped Classical _root_.NumberField _root_.Matrix _root_.Matrix.Norms.Elementwise
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicSecondProjection.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

theorem native_wedge_jacobi_coefficient (a b : RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.Cotangent) :
    RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge a b ![![1, 0], ![0, 1]] =
      RepresentationTheory.Theta.Kernel.Calculus.wedgeCoefficient (SparseSpanning.CM.jacobiCoefficients (Fin 2) a) (SparseSpanning.CM.jacobiCoefficients (Fin 2) b) := by
  rw [RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.wedge_apply]
  have h0 : (![1, 0] : HeckeCycles.GeometricSource.CM.BallChart) = Pi.single 0 1 := by
    funext i
    fin_cases i <;> simp
  have h1 : (![0, 1] : HeckeCycles.GeometricSource.CM.BallChart) = Pi.single 1 1 := by
    funext i
    fin_cases i <;> simp
  rw [h0, h1]
  have hc (l : RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.Cotangent) (i : Fin 2) :
      SparseSpanning.CM.jacobiCoefficients (Fin 2) l i = l (Pi.single i 1) := by
    apply congrArg l
    funext k
    simp only [Pi.single_apply]
    split_ifs <;> rfl
  simp only [RepresentationTheory.Theta.Kernel.Calculus.wedgeCoefficient, hc]

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} (d : Fin 2 → Gal(K/ℚ) → Bool)
  (Q : Lagrangians.CM.LagrangianPair K B places (fun k v => d k (places.representative v)))
  (hμ : ∀ k, d k (places.representative places.distinguished) = true)
  (D : SourceIntrinsicKernel.CM.SourceNativeThetaKernelData K Q hμ)
  (L : (j : Fin 2) → HeckeCycles.GeometricSource.CM.LinePeriod K B places (d j))
  (hL : ∀ j, (L j).coordinates.a = Q.a j ∧ (L j).coordinates.delta = Q.delta)

include D hL in
theorem native_source_total_coefficient_factorization (Φ : RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (PeriodTotal.CM.TotalPositions K places)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ (n : ℕ) (φ ψ : Fin n → RepresentationTheory.Theta.Kernel.Definitions.DerivativeFactorization.Input (HeckeCycles.GeometricSource.CM.Positions K places)),
      ∀ z : B.Domain, InitialTensor.CM.splitThetaTopCoefficient K (L 0) (L 1) Φ z.val =
        ∑ i, c * Slots.CM.sourceWedgeCoefficient K (L 0) (L 1) (φ i) (ψ i) z.val := by
  let hC := D.total_valid.2.2.2.2.1
  let hG := D.total_valid.2.2.2.2.2.1
  let f := IntrinsicKernelSum.CM.sumComparisonFiniteInput K Q hμ D.total.comparison hC (fun j => (L j).coordinates) hL Φ
  obtain ⟨c, hc, n, φ, ψ, hfactor⟩ := SourceIntrinsicKernelFactorization.CM.source_native_c38_factorization K d Q hμ D L hL f
  let z₀ := SourceIntrinsicBall.CM.nativeSourceBallPoint K B RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic.origin
  let κ := IntrinsicKernelSumSlots.CM.sumComparisonTopConstant K d Q hμ D.total.comparison hC L hL z₀
  have hκ : κ ≠ 0 := IntrinsicKernelSumSlots.CM.sum_comparison_top_constant_ne_zero K d Q hμ D.total.comparison hC hG L hL z₀
  refine ⟨c / κ, div_ne_zero hc hκ, n, φ, ψ, ?_⟩
  intro z
  have hn := IntrinsicKernelSumSlots.CM.sum_comparison_native_top K d Q hμ D.total.comparison hC hG L hL Φ z₀ z
  have he := congrArg (fun ω : RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.TopCovector => ω ![![1, 0], ![0, 1]]) (hn.symm.trans (hfactor z))
  simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
    smul_eq_mul, RepresentationTheory.Theta.Kernel.IntrinsicExterior.Intrinsic.area_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, sub_zero, native_wedge_jacobi_coefficient] at he
  change κ * InitialTensor.CM.splitThetaTopCoefficient K (L 0) (L 1) Φ z.val =
    ∑ i, c * Slots.CM.sourceWedgeCoefficient K (L 0) (L 1) (φ i) (ψ i) z.val at he
  apply mul_left_cancel₀ hκ
  rw [he, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicSourceTotalFactorization.CM
