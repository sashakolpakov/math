import OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame
import OAI.RepresentationTheory.Theta.Adelic.SmoothSquareRoot
import OAI.RepresentationTheory.Theta.Adelic.MatrixSmoothness

/-! # Geometric Frame Smoothness -/

namespace OAI.RepresentationTheory.Theta.Adelic.GeometricFrameSmoothness

noncomputable section

/-! Smoothness of the actual period, inverse position frame, and
half-determinant frame in the affine ball coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open _root_.Matrix
open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates
open OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic OAI.RepresentationTheory.Theta.Adelic.GeometricHalfFrame
open OAI.RepresentationTheory.Theta.Adelic.BallHolomorphicSquare OAI.RepresentationTheory.Theta.Adelic.SmoothSquareRoot OAI.RepresentationTheory.Theta.Adelic.MatrixSmoothness

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

theorem rawGeometricFrame_smooth (a : BallGeometryData.FrameIndex A → ℂ) :
    ContDiff ℝ ⊤ (fun z => PeriodHolomorphic.rawGeometricFrame A z a) := by
  apply contDiff_pi.mpr
  intro v
  apply ContDiff.prodMk
  · apply contDiff_pi.mpr
    rintro ⟨i, j⟩
    by_cases hv : v = A.distinguished
    · fin_cases i <;> simp [hv, DeterminantCoordinates.lineVector] <;> fun_prop
    · cases A.positive v j <;> simp [hv] <;> fun_prop
  · apply contDiff_pi.mpr
    rintro ⟨i, j⟩
    by_cases hv : v = A.distinguished
    · fin_cases i <;> simp [hv, DeterminantCoordinates.annihilatorVector] <;> fun_prop
    · cases A.positive v j <;> simp [hv] <;> fun_prop

variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

theorem rawCoordinateHodgeMatrix_smooth : ContDiff ℝ ⊤ (PeriodHolomorphic.rawCoordinateHodgeMatrix A P) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_apply ℝ ℂ i).comp
    (((ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm.toContinuousLinearMap.restrictScalars ℝ).contDiff.comp
      (rawGeometricFrame_smooth A (Pi.single j 1)))

theorem rawHodgePosition_smooth : ContDiff ℝ ⊤ (PeriodHolomorphic.rawHodgePosition A P) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ⊤ (fun z => PeriodHolomorphic.rawCoordinateHodgeMatrix A P z (.inl i) j)
  exact (contDiff_apply_apply ℝ ℂ (.inl i) j).comp (rawCoordinateHodgeMatrix_smooth A P)

theorem rawHodgeMomentum_smooth : ContDiff ℝ ⊤ (PeriodHolomorphic.rawHodgeMomentum A P) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  change ContDiff ℝ ⊤ (fun z => PeriodHolomorphic.rawCoordinateHodgeMatrix A P z (.inr i) j)
  exact (contDiff_apply_apply ℝ ℂ (.inr i) j).comp (rawCoordinateHodgeMatrix_smooth A P)

theorem period_matrix_smooth : BallGeometryData.BallSmooth (fun z => (PeriodCoordinates.geometricPeriod A P z).matrix) := by
  have hi : ContDiffOn ℝ ⊤ (fun z => (PeriodHolomorphic.rawHodgePosition A P z)⁻¹) BallGeometryData.ballDomain :=
    MatrixSmoothness.matrix_inverse_contDiffOn (PeriodHolomorphic.rawHodgePosition A P) (rawHodgePosition_smooth A P).contDiffOn
    (fun z hz => PeriodCoordinates.hodgePosition_det_ne_zero A P ⟨z, hz⟩)
  have hp := MatrixSmoothness.matrix_product_contDiffOn (PeriodHolomorphic.rawHodgeMomentum A P) (fun z => (PeriodHolomorphic.rawHodgePosition A P z)⁻¹)
    (rawHodgeMomentum_smooth A P).contDiffOn hi
  apply hp.congr
  intro z hz
  rw [dite_eq_left hz]
  rfl

theorem position_inverse_smooth : BallGeometryData.BallSmooth (fun z => (PeriodCoordinates.geometricPositionUnit A P z).inv) := by
  have hi : ContDiffOn ℝ ⊤ (fun z => (PeriodHolomorphic.rawHodgePosition A P z)⁻¹) BallGeometryData.ballDomain :=
    MatrixSmoothness.matrix_inverse_contDiffOn (PeriodHolomorphic.rawHodgePosition A P) (rawHodgePosition_smooth A P).contDiffOn
    (fun z hz => PeriodCoordinates.hodgePosition_det_ne_zero A P ⟨z, hz⟩)
  apply hi.congr
  intro z hz
  rw [dite_eq_left hz]
  exact Matrix.coe_units_inv (PeriodCoordinates.geometricPositionUnit A P ⟨z, hz⟩)

theorem position_determinant_smooth : BallGeometryData.BallSmooth (fun z => (PeriodCoordinates.geometricPositionUnit A P z).val.det) := by
  have hd : ContDiffOn ℝ ⊤ (fun z => (PeriodHolomorphic.rawHodgePosition A P z).det) BallGeometryData.ballDomain :=
    (MatrixSmoothness.matrix_determinant_contDiff.comp (rawHodgePosition_smooth A P)).contDiffOn
  apply hd.congr
  intro z hz
  rw [dite_eq_left hz]
  rfl

theorem half_frame_smooth : BallGeometryData.BallSmooth (GeometricHalfFrame.geometricHalfFrame A P) :=
  SmoothSquareRoot.ball_smooth_of_continuous_square (GeometricHalfFrame.geometricHalfFrame A P)
    (fun z => (PeriodCoordinates.geometricPositionUnit A P z).val.det)
    (BallHolomorphicSquare.ball_holomorphic_continuous _ (GeometricHalfFrame.geometricHalfFrame_holomorphic A P))
    (position_determinant_smooth A P) (GeometricHalfFrame.geometricHalfFrame_square A P) (GeometricHalfFrame.geometricHalfFrame_nonzero A P)

end

end OAI.RepresentationTheory.Theta.Adelic.GeometricFrameSmoothness
