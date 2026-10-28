import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualFamily
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualShearDifference

/-! # Intrinsic Residual Multiplier -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualMultiplier.Intrinsic

noncomputable section

/-! Exact global values of the actual residual Schwartz operator. Its
multiplier is the residual quadratic form, with the native character normalization. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualFamily.IntrinsicFamily OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualShearDifference.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualField.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualEquiv.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalResidualAction.IntrinsicShear OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionFixedShear.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0} {C : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)

local instance (w : NumberField.InfinitePlace F) : MeasurableSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := borel _
local instance (w : NumberField.InfinitePlace F) : BorelSpace (Weil.AdelicSplitting.ArchimedeanAdeles.Construction.Completion F (.inl w)) := ⟨rfl⟩

def residualArchOperator : Adelic.ThetaEvaluation.ArchimedeanTests F 6 ≃ₗ[ℂ] Adelic.ThetaEvaluation.ArchimedeanTests F 6 :=
  IntrinsicMultiplicityOperator.IntrinsicCommutingArch.archOperator F C (IntrinsicResidualFamily.IntrinsicFamily.residualOscillatorFamily B hC hG hO)

theorem residual_quadratic_local_sum (q : Adelic.BallGeometryData.RealPositions A) :
    (∑ v : Fin A.places, Weil.Local.FunctionsMetaplectic.Construction.quadratic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v IntrinsicBallTopology.Intrinsic.origin).val (q v)) =
      IntrinsicResidualShearDifference.Intrinsic.residualQuadraticForm B q / 2 := by
  have hv (v : Fin A.places) :
      (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v IntrinsicBallTopology.Intrinsic.origin).val.mulVec (q v) =
        fun i => IntrinsicResidualPhase.Intrinsic.residualPhase B (IntrinsicResidualShearDifference.Intrinsic.purePositions q) v (.inr i) := by
    have hs := IntrinsicPositionFixedShear.Intrinsic.shear_matrix_apply
      (IntrinsicLocalResidualEquiv.Intrinsic.localResidualContinuousEquiv B hC hG hO v IntrinsicBallTopology.Intrinsic.origin).toLinearMap (q v)
    have hr := IntrinsicLocalResidualEquiv.Intrinsic.local_residual_apply B hC hG hO v IntrinsicBallTopology.Intrinsic.origin (IntrinsicResidualShearDifference.Intrinsic.purePositions q)
    exact hs.trans (congrArg (fun t : Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 => fun i => t (.inr i)) hr)
  simp_rw [Weil.AdelicSplitting.NonarchimedeanIntertwiner.LocalAnalysis.quadratic_eq_dot,hv]
  rw [← Finset.sum_div]
  rfl

def residualPhaseMultiplier (q : Adelic.BallGeometryData.RealPositions A) : ℂ :=
  Complex.exp ((Real.pi : ℂ) * Complex.I * (IntrinsicResidualShearDifference.Intrinsic.residualQuadraticForm B q : ℂ))

theorem residual_phase_multiplier_ne (q : Adelic.BallGeometryData.RealPositions A) : residualPhaseMultiplier B q ≠ 0 :=
  Complex.exp_ne_zero _

theorem residual_character_product (q : Adelic.BallGeometryData.RealPositions A) :
    (∏ v : Fin A.places, Weil.Local.Gaussian.Construction.realCharacter 1
      (Weil.Local.FunctionsMetaplectic.Construction.quadratic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v IntrinsicBallTopology.Intrinsic.origin).val (q v))) =
        residualPhaseMultiplier B q := by
  simp_rw [Weil.Local.Gaussian.Construction.realCharacter_apply]
  rw [← Complex.exp_sum]
  have he := residual_quadratic_local_sum B hC hG hO q
  have hc := congrArg (fun t : ℝ => (t : ℂ)) he
  simp only [Complex.ofReal_sum,Complex.ofReal_div,Complex.ofReal_ofNat] at hc
  unfold residualPhaseMultiplier
  congr 1
  simp only [Complex.ofReal_mul,mul_one,Complex.ofReal_ofNat]
  rw [← Finset.sum_mul,← Finset.mul_sum,hc]
  ring

theorem residual_arch_value (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) (q : Adelic.BallGeometryData.RealPositions A) :
    Adelic.DataTheta.archTestValue (A := A) (residualArchOperator B hC hG hO φ) q =
      residualPhaseMultiplier B q * Adelic.DataTheta.archTestValue (A := A) φ q := by
  have hv (v : Fin A.places) :
      ((residualArchOperator B hC hG hO φ) (A.enumerate v)).val
        (fun i => (A.real v).symm (q v i)) =
      Weil.Local.Gaussian.Construction.realCharacter 1 (Weil.Local.FunctionsMetaplectic.Construction.quadratic (IntrinsicLocalResidualAction.IntrinsicShear.localResidualSymmetricMatrix B hC hG hO v IntrinsicBallTopology.Intrinsic.origin).val (q v)) *
        (φ (A.enumerate v)).val (fun i => (A.real v).symm (q v i)) := by
    change (Weil.AdelicSplitting.Oscillator.Construction.localOperator _ _ _ (IntrinsicResidualFamily.IntrinsicFamily.residualOscillatorFamily B hC hG hO (A.enumerate v))
      (φ (A.enumerate v))).val _ = _
    rw [IntrinsicResidualFamily.IntrinsicFamily.residual_family_at]
    exact IntrinsicLocalResidualField.Intrinsic.local_residual_field_operator_value B hC hG hO v IntrinsicBallTopology.Intrinsic.origin hψ _ _
  unfold Adelic.DataTheta.archTestValue
  simp_rw [hv]
  rw [Finset.prod_mul_distrib,residual_character_product]

theorem residual_arch_inverse_value (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) (q : Adelic.BallGeometryData.RealPositions A) :
    Adelic.DataTheta.archTestValue (A := A) ((residualArchOperator B hC hG hO).symm φ) q =
      (residualPhaseMultiplier B q)⁻¹ * Adelic.DataTheta.archTestValue (A := A) φ q := by
  have he := residual_arch_value B hC hG hO hψ ((residualArchOperator B hC hG hO).symm φ) q
  rw [LinearEquiv.apply_symm_apply] at he
  rw [he,← mul_assoc,inv_mul_cancel₀ (residual_phase_multiplier_ne B q),one_mul]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualMultiplier.Intrinsic
