import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualMultiplier
import OAI.RepresentationTheory.Theta.Kernel.LinearOperatorFixedLevel
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase

/-! # Intrinsic Residual Difference Operator -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualDifferenceOperator.Intrinsic

noncomputable section

/-! The difference of native residual operators is an actual Schwartz
operator whose rational multiplier is exactly the compact finite transport phase. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.DataTheta.Descent OAI.RepresentationTheory.Theta.Adelic.ThetaEvaluation
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SiegelBranchData OAI.RepresentationTheory.Theta.Adelic.Evaluation OAI.RepresentationTheory.Theta.Adelic.FiniteSchwartz
open OAI.RepresentationTheory.Theta.Adelic.SpecialUnitaryTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualFamily.IntrinsicFamily OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualShearDifference.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualMultiplier.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicQuadraticPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicMultiplicityOperator.IntrinsicCommutingArch OAI.RepresentationTheory.Theta.Kernel.IntrinsicArchimedeanIndependence.Intrinsic

theorem inverse_linear_commutes {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : V ≃ₗ[ℂ] V) (T : V → V) (h : ∀ x, L (T x) = T (L x)) (x : V) :
    L.symm (T x) = T (L.symm x) := by
  apply L.injective
  rw [L.apply_symm_apply,h,L.apply_symm_apply]

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K} {hd : d ≠ 0}
variable {C Cp : Weil.AdelicSplitting.Characters.Construction.GlobalCharacters F d 3 2}
variable {D : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd C P}
variable {Dp : Weil.AdelicSplitting.Assembly.Construction.NormalizedLocalSplittings F d 3 2 H K hd Cp P}
variable (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
variable (hO : Adelic.DataTheta.OscillatorIdentification B P hd C D)
variable (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hGp : Adelic.DataTheta.GeometryIdentification Bp)
variable (hOp : Adelic.DataTheta.OscillatorIdentification Bp P hd Cp Dp)

def residualDifferenceOperator : Adelic.ThetaEvaluation.ArchimedeanTests F 6 ≃ₗ[ℂ] Adelic.ThetaEvaluation.ArchimedeanTests F 6 :=
  (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp).trans (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator B hC hG hO).symm

theorem residual_difference_commutes
    (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (hψp : Adelic.DataTheta.Descent.StandardArchCharacter (A := IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) Cp.ψ) (heq : Cp.ψ = C.ψ)
    (hu : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd C D) (hup : Adelic.SiegelBranchData.ArchimedeanLiftUniqueness P hd Cp Dp)
    (g : Adelic.RationalSU.ArchimedeanSU F H) (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) :
    residualDifferenceOperator p B Bp hC hG hO hCp hGp hOp
      (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g φ) =
    Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g
      (residualDifferenceOperator p B Bp hC hG hO hCp hGp hOp φ) := by
  have hbase (η : Adelic.ThetaEvaluation.ArchimedeanTests F 6) :
      IntrinsicResidualMultiplier.Intrinsic.residualArchOperator B hC hG hO (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g η) =
        Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator B hC hG hO η) :=
    IntrinsicMultiplicityOperator.IntrinsicCommutingArch.arch_operator_commutes F H K hd P C D _ (IntrinsicResidualFamily.IntrinsicFamily.residual_family_commutes B hC hG hO hψ hu) g η
  have hother (η : Adelic.ThetaEvaluation.ArchimedeanTests F 6) :
      IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g η) =
        Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp η) := by
    have hi := IntrinsicArchimedeanIndependence.Intrinsic.archimedeanAction_independent F H K hd P C Cp D Dp heq hu g η
    have hc := IntrinsicMultiplicityOperator.IntrinsicCommutingArch.arch_operator_commutes F H K hd P Cp Dp _
      (IntrinsicResidualFamily.IntrinsicFamily.residual_family_commutes Bp hCp hGp hOp hψp hup) g η
    exact (congrArg (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp) hi.symm).trans
      (hc.trans (IntrinsicArchimedeanIndependence.Intrinsic.archimedeanAction_independent F H K hd P C Cp D Dp heq hu g _))
  change (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator B hC hG hO).symm
    (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp (Adelic.SpecialUnitaryTheta.archimedeanAction F H K hd C P D g φ)) = _
  rw [hother]
  exact inverse_linear_commutes _ _ hbase _

include hC hCp in
theorem residual_phase_ratio_rational (x : Fin 6 → F) :
    (IntrinsicResidualMultiplier.Intrinsic.residualPhaseMultiplier B (Adelic.BallGeometryData.archPositions A x))⁻¹ *
      IntrinsicResidualMultiplier.Intrinsic.residualPhaseMultiplier Bp (Adelic.BallGeometryData.archPositions A x) =
        IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x := by
  have he := IntrinsicResidualShearDifference.Intrinsic.compact_rational_shear_residual_difference p B Bp hC hCp x
  have hc := congrArg (fun t : ℝ => (t : ℂ)) he
  simp only [Complex.ofReal_ratCast,Complex.ofReal_sub] at hc
  unfold IntrinsicResidualMultiplier.Intrinsic.residualPhaseMultiplier IntrinsicQuadraticPhase.Intrinsic.quadraticPhase
  rw [← Complex.exp_neg,← Complex.exp_add]
  congr 1
  change -((Real.pi : ℂ) * Complex.I * (IntrinsicResidualShearDifference.Intrinsic.residualQuadraticForm B (Adelic.BallGeometryData.archPositions A x) : ℂ)) +
      (Real.pi : ℂ) * Complex.I * (IntrinsicResidualShearDifference.Intrinsic.residualQuadraticForm Bp (Adelic.BallGeometryData.archPositions A x) : ℂ) =
        (Real.pi : ℂ) * Complex.I * ((-(IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp x x) : ℚ) : ℂ)
  rw [Rat.cast_neg,hc]
  ring

theorem arch_value_real_coordinates (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) (x : Fin 6 → F) :
    Adelic.ThetaEvaluation.archimedeanValue F 6 φ x = Adelic.DataTheta.archTestValue (A := A) φ (Adelic.BallGeometryData.archPositions A x) := by
  simp only [Adelic.ThetaEvaluation.archimedeanValue,Adelic.DataTheta.archTestValue,Adelic.BallGeometryData.archPositions,RingEquiv.symm_apply_apply]
  exact (Equiv.prod_comp A.enumerate (fun v => (φ v).val
    (fun i => Weil.AdelicSplitting.ArchimedeanAdeles.Construction.rationalScalar F (.inl v) (x i)))).symm

theorem residual_difference_rational_value
    (hψ : Adelic.DataTheta.Descent.StandardArchCharacter (A := A) C.ψ)
    (hψp : Adelic.DataTheta.Descent.StandardArchCharacter (A := IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) Cp.ψ)
    (φ : Adelic.ThetaEvaluation.ArchimedeanTests F 6) (x : Fin 6 → F) :
    Adelic.ThetaEvaluation.archimedeanValue F 6 (residualDifferenceOperator p B Bp hC hG hO hCp hGp hOp φ) x =
      IntrinsicQuadraticPhase.Intrinsic.quadraticPhase F 6 (-IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp) x * Adelic.ThetaEvaluation.archimedeanValue F 6 φ x := by
  rw [arch_value_real_coordinates (A := A),arch_value_real_coordinates (A := A)]
  change Adelic.DataTheta.archTestValue (A := A) ((IntrinsicResidualMultiplier.Intrinsic.residualArchOperator B hC hG hO).symm
    (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp φ)) (Adelic.BallGeometryData.archPositions A x) = _
  rw [IntrinsicResidualMultiplier.Intrinsic.residual_arch_inverse_value B hC hG hO hψ]
  have hp := IntrinsicResidualMultiplier.Intrinsic.residual_arch_value Bp hCp hGp hOp hψp φ (Adelic.BallGeometryData.archPositions A x)
  change Adelic.DataTheta.archTestValue (A := A) (IntrinsicResidualMultiplier.Intrinsic.residualArchOperator Bp hCp hGp hOp φ) (Adelic.BallGeometryData.archPositions A x) =
    IntrinsicResidualMultiplier.Intrinsic.residualPhaseMultiplier Bp (Adelic.BallGeometryData.archPositions A x) * Adelic.DataTheta.archTestValue (A := A) φ (Adelic.BallGeometryData.archPositions A x) at hp
  rw [hp,← mul_assoc,residual_phase_ratio_rational p B Bp hC hCp]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualDifferenceOperator.Intrinsic
