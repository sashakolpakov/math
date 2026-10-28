import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SourceGeometricFrame

/-! # Intrinsic Kernel Sum Model -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumModel.CM

noncomputable section

/-! The actual orthogonal sum used by native ThetaKernel has the original
two-line skew form, multiplicity basis and positive geometric frame. -/

open scoped Classical _root_.NumberField _root_.Matrix
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic

section

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (a : Fin 2 → K) (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)

theorem direct_source_sum_skew_unit :
    RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic.blockUnit (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 0) (ha 0) (ha0 0))
      (SingleLineArithmetic.CM.directSingleLineSkewUnit K δ hδ hδ0 (a 1) (ha 1) (ha0 1)) =
        BallArithmetic.CM.directSourceSkewUnit K δ hδ hδ0 a ha ha0 := by
  apply Units.ext
  change Matrix.diagonal ![_, _] = _
  rw [QuadraticMultiplicityBasis.CM.direct_source_skew_unit_diagonal, SingleLineTrace.CM.direct_single_line_skew_unit_diagonal,
    SingleLineTrace.CM.direct_single_line_skew_unit_diagonal]
  simp only [Matrix.diagonal_apply_eq]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem direct_source_sum_skew_basis (places : HeckeCycles.GeometricSource.CM.Places K) (v : Fin places.count) :
    RepresentationTheory.Theta.Kernel.IntrinsicSplitting.IntrinsicArithmetic.blockUnit (CMOrthonormalFrames.CM.singleLineSkewNormalizer K δ hδ hδ0 (a 0) (ha 0) (ha0 0) places v)
      (CMOrthonormalFrames.CM.singleLineSkewNormalizer K δ hδ hδ0 (a 1) (ha 1) (ha0 1) places v) =
        CMOrthonormalFrames.CM.sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 v := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

end

attribute [local instance] BallArithmetic.CM.directNativeRealNumberField

variable (K : IntermediateField ℚ ℂ) [NumberField K] [IsCMField K] [IsGalois ℚ K]
  {B : HeckeCycles.GeometricSource.CM.BallDatum K} {places : HeckeCycles.GeometricSource.CM.Places K} {d : Fin 2 → Fin places.count → Bool}
  (Q : Lagrangians.CM.LagrangianPair K B places d) (hμ : ∀ j, d j places.distinguished = true)

theorem native_c38_sum_basis (v : Fin places.count) :
    (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ).basisP v =
      (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place).basisP v :=
  direct_source_sum_skew_basis K Q.delta Q.delta_imaginary Q.delta_ne_zero Q.a
    (BallArithmetic.CM.direct_source_a_fixed K Q) (BallArithmetic.CM.direct_source_a_ne_zero K Q) places v

theorem native_c38_sum_positive (v : Fin places.count) (j : Fin 2) :
    (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ).positive v j =
      (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place).positive v j := by
  fin_cases j <;> rfl

theorem native_c38_sum_geometric_frame (z : RepresentationTheory.Theta.Adelic.BallNatural.Ball)
    (u : Fin places.count × (Fin 3 × Fin 2) → ℂ) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (IntrinsicKernelArithmetic.CM.directSourceNativeSumArithmetic K Q hμ) z u =
      RepresentationTheory.Theta.Adelic.BallGeometryData.geometricFrame (BallArithmetic.CM.directSourceBallArithmeticData K Q hμ B.other_place) z u := by
  funext v
  apply Prod.ext <;> funext i
  rcases i with ⟨i, j⟩
  · fin_cases j <;> rfl
  · rcases i with ⟨i, j⟩
    fin_cases j <;> rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.IntrinsicKernelSumModel.CM
