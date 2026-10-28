import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv

/-! # Intrinsic Residual Shear Difference -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualShearDifference.Intrinsic

noncomputable section

/-! The rational phase in the exact compact kernel comparison is the
difference of the two actual native residual quadratic forms. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactShear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualPhase.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualEquiv.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCotangentAction.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicLocalJacobiPhase.Intrinsic

theorem pairing_shear_difference {I J V : Type} [Fintype I] [Fintype J] [Fintype V]
    (u v : V → (J ⊕ J) → ℝ) (q : V → J → ℝ) (t : (I ⊕ I) → ℝ) (b : I → ℝ)
    (hu : ∀ w i, u w (.inl i) = q w i) (hv : ∀ w i, v w (.inl i) = q w i)
    (he : Adelic.DataTheta.standardPairing t (Sum.elim b (0 : I → ℝ)) =
      ∑ w, Adelic.DataTheta.standardPairing (u w) (v w)) :
    (∑ i, t (.inr i) * b i) =
      (∑ w, ∑ i, q w i * u w (.inr i)) - (∑ w, ∑ i, q w i * v w (.inr i)) := by
  simp only [Adelic.DataTheta.standardPairing,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,mul_zero,zero_sub,
    Finset.sum_neg_distrib,hu,hv,Finset.sum_sub_distrib] at he
  have hcomm : (∑ w, ∑ i, u w (.inr i) * q w i) = (∑ w, ∑ i, q w i * u w (.inr i)) := by
    apply Finset.sum_congr rfl
    intro w _
    apply Finset.sum_congr rfl
    intro i _
    exact mul_comm _ _
  rw [hcomm] at he
  linarith

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

def purePositions (q : Adelic.BallGeometryData.RealPositions A) : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 :=
  fun v => Sum.elim (q v) (0 : Fin 6 → ℝ)

def residualQuadraticForm (B : Adelic.DataTheta.ComparisonData F H K A) (q : Adelic.BallGeometryData.RealPositions A) : ℝ :=
  ∑ v, ∑ i, q v i * IntrinsicResidualPhase.Intrinsic.residualPhase B (purePositions q) v (.inr i)

theorem residual_pure_phase (B : Adelic.DataTheta.ComparisonData F H K A) (q : Adelic.BallGeometryData.RealPositions A) :
    B.realPhase (IntrinsicResidualPhase.Intrinsic.residualPhase B (purePositions q)) =
      Sum.elim (B.realPosition q) (0 : Adelic.BallGeometryData.FrameIndex A → ℝ) := by
  unfold IntrinsicResidualPhase.Intrinsic.residualPhase
  rw [B.realPhase.apply_symm_apply]
  change Sum.elim (B.realPosition q) (IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B 0) = _
  rw [show IntrinsicLocalJacobiPhase.Intrinsic.globalRealMomentum B 0 = 0 from (IntrinsicMomentumEquiv.Intrinsic.momentumLinearEquiv B).map_zero]

variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_real_shear_residual_difference (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (q : Adelic.BallGeometryData.RealPositions A) :
    (∑ i, IntrinsicCompactRealPhase.Intrinsic.compactRealPhaseChange p B Bp
      (Sum.elim (B.realPosition q) (0 : Adelic.BallGeometryData.FrameIndex A → ℝ)) (.inr i) * Bp.realPosition q i) =
      residualQuadraticForm B q - residualQuadraticForm Bp q := by
  let u : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 := IntrinsicResidualPhase.Intrinsic.residualPhase B (purePositions q)
  let v : Fin A.places → Weil.Local.FunctionsMetaplectic.Construction.PhaseSpace ℝ 6 :=
    IntrinsicResidualPhase.Intrinsic.residualPhase (A := IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) Bp (purePositions q)
  have hu : (fun w i => u w (.inl i)) = q := IntrinsicResidualPhase.Intrinsic.residual_phase_positions B hC (purePositions q)
  have hv : (fun w i => v w (.inl i)) = q := IntrinsicResidualPhase.Intrinsic.residual_phase_positions Bp hCp (purePositions q)
  have he : Adelic.DataTheta.standardPairing (I := Adelic.BallGeometryData.FrameIndex A) (Bp.realPhase u) (Bp.realPhase v) =
      ∑ w : Fin A.places, Adelic.DataTheta.standardPairing (u w) (v w) := hCp.2.2.2.2.2.1 u v
  have hz : Bp.realPhase v = Sum.elim (Bp.realPosition q) (0 : Adelic.BallGeometryData.FrameIndex A → ℝ) :=
    residual_pure_phase Bp q
  have hx : Bp.realPhase u = IntrinsicCompactRealPhase.Intrinsic.compactRealPhaseChange p B Bp
      (Sum.elim (B.realPosition q) (0 : Adelic.BallGeometryData.FrameIndex A → ℝ)) := by
    have h := residual_pure_phase B q
    have ht := congrArg (fun y => Bp.realPhase (B.realPhase.symm y)) h
    rw [B.realPhase.symm_apply_apply] at ht
    exact ht
  rw [hz,hx] at he
  exact pairing_shear_difference u v q _ (Bp.realPosition q)
    (fun w i => congrFun (congrFun hu w) i) (fun w i => congrFun (congrFun hv w) i) he

theorem compact_real_phase_rational (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (u : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℚ) :
    IntrinsicCompactRealPhase.Intrinsic.compactRealPhaseChange p B Bp (fun i => (u i : ℝ)) =
      fun i => (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPhaseChange p B Bp u i : ℝ) := by
  have hr := IntrinsicCompactRealPhase.Intrinsic.compact_phase_change_real p B Bp hC hCp (fun i => (u i : ℝ))
  simp only [Complex.ofReal_ratCast] at hr
  rw [IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp] at hr
  funext i
  exact Complex.ofReal_injective ((congrFun hr i).symm.trans (Complex.ofReal_ratCast _).symm)

theorem compact_rational_shear_residual_difference (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : Fin 6 → F) :
    (IntrinsicCompactShear.Intrinsic.compactShearBilinear p B Bp x x : ℝ) =
      residualQuadraticForm B (Adelic.BallGeometryData.archPositions A x) - residualQuadraticForm Bp (Adelic.BallGeometryData.archPositions A x) := by
  have he := compact_real_shear_residual_difference p B Bp hC hCp (Adelic.BallGeometryData.archPositions A x)
  have hB : B.realPosition (Adelic.BallGeometryData.archPositions A x) = fun i => (B.rationalPosition x i : ℝ) :=
    funext (hC.1 x)
  have hp : Bp.realPosition (Adelic.BallGeometryData.archPositions A x) = fun i => (Bp.rationalPosition x i : ℝ) :=
    funext (hCp.1 x)
  rw [hB,hp] at he
  have hi : Sum.elim (fun i => (B.rationalPosition x i : ℝ)) (0 : Adelic.BallGeometryData.FrameIndex A → ℝ) =
      fun i => ((Sum.elim (B.rationalPosition x) (0 : Adelic.BallGeometryData.FrameIndex A → ℚ)) i : ℝ) := by
    funext i
    cases i <;> simp
  rw [hi,compact_real_phase_rational p B Bp hC hCp] at he
  simp only [IntrinsicCompactShear.Intrinsic.compactShearBilinear_apply,Rat.cast_sum,Rat.cast_mul]
  exact he

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicResidualShearDifference.Intrinsic
