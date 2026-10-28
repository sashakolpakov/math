import OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus

/-! # Period Holomorphic -/

namespace OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic

noncomputable section

/-! The constructed position frame and Siegel period are holomorphic
in the actual affine ball coordinates. -/

open scoped Classical _root_.NumberField _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.BallNatural
open OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates OAI.RepresentationTheory.Theta.Adelic.ComplexPhaseCoordinates OAI.RepresentationTheory.Theta.Adelic.PeriodCoordinates

variable {F : Type} [Field F] [NumberField F] {d : F} {m : ℕ}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin m) (Fin m) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : BallGeometryData.BallArithmeticData F d m H K)

def rawGeometricFrame (z : Fin 2 → ℂ) (a : BallGeometryData.FrameIndex A → ℂ) : BallGeometryData.ComplexPhase A :=
  fun v =>
    (fun ij => if v = A.distinguished then DeterminantCoordinates.lineVector z ij.1 * a (v, 0, ij.2)
      else if A.positive v ij.2 then a (v, ij) else 0,
     fun ij => if v = A.distinguished then
        DeterminantCoordinates.annihilatorVector z 0 ij.1 * a (v, 1, ij.2) +
          DeterminantCoordinates.annihilatorVector z 1 ij.1 * a (v, 2, ij.2)
      else if A.positive v ij.2 then 0 else a (v, ij))

theorem rawGeometricFrame_holomorphic (a : BallGeometryData.FrameIndex A → ℂ) :
    Differentiable ℂ (fun z => rawGeometricFrame A z a) := by
  apply differentiable_pi.mpr
  intro v
  apply Differentiable.prodMk
  · apply differentiable_pi.mpr
    rintro ⟨i, j⟩
    by_cases hv : v = A.distinguished
    · fin_cases i <;> simp [hv, DeterminantCoordinates.lineVector] <;> fun_prop
    · cases A.positive v j <;> simp [hv]
  · apply differentiable_pi.mpr
    rintro ⟨i, j⟩
    by_cases hv : v = A.distinguished
    · fin_cases i <;> simp [hv, DeterminantCoordinates.annihilatorVector]
      fun_prop
    · cases A.positive v j <;> simp [hv]

variable (P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 m H K)

def rawCoordinateHodgeMatrix (z : Fin 2 → ℂ) :
    Matrix (BallGeometryData.FrameIndex A ⊕ BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  fun i j => (ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm (rawGeometricFrame A z (Pi.single j 1)) i

def rawHodgePosition (z : Fin 2 → ℂ) : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  (rawCoordinateHodgeMatrix A P z).submatrix Sum.inl id

def rawHodgeMomentum (z : Fin 2 → ℂ) : Matrix (BallGeometryData.FrameIndex A) (BallGeometryData.FrameIndex A) ℂ :=
  (rawCoordinateHodgeMatrix A P z).submatrix Sum.inr id

theorem rawCoordinateHodgeMatrix_holomorphic : Differentiable ℂ (rawCoordinateHodgeMatrix A P) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  exact (differentiable_apply i).comp
    ((ComplexPhaseCoordinates.complexPhaseCoordinates A P).symm.differentiable.comp (rawGeometricFrame_holomorphic A _))

theorem rawHodgePosition_holomorphic : Differentiable ℂ (rawHodgePosition A P) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  exact (differentiable_apply j).comp
    ((differentiable_apply (.inl i)).comp (rawCoordinateHodgeMatrix_holomorphic A P))

theorem rawHodgeMomentum_holomorphic : Differentiable ℂ (rawHodgeMomentum A P) := by
  apply differentiable_pi.mpr
  intro i
  apply differentiable_pi.mpr
  intro j
  exact (differentiable_apply j).comp
    ((differentiable_apply (.inr i)).comp (rawCoordinateHodgeMatrix_holomorphic A P))

theorem position_frame_holomorphic : BallGeometryData.BallHolomorphic (fun z => (PeriodCoordinates.geometricPositionUnit A P z).val) := by
  apply (rawHodgePosition_holomorphic A P).differentiableOn.congr
  intro z hz
  rw [dite_eq_left hz]
  rfl

theorem period_matrix_holomorphic : BallGeometryData.BallHolomorphic (fun z => (PeriodCoordinates.geometricPeriod A P z).matrix) := by
  have hi : DifferentiableOn ℂ (fun z => (rawHodgePosition A P z)⁻¹) BallGeometryData.ballDomain :=
    AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_inverse_holomorphic _
      (rawHodgePosition_holomorphic A P).differentiableOn
      (fun z hz => PeriodCoordinates.hodgePosition_det_ne_zero A P ⟨z, hz⟩)
  have hp := AlgebraicGeometry.HodgeConjecture.ThetaCycle.MatrixCalculus.CM.matrix_product_holomorphic (rawHodgeMomentum A P)
    (fun z => (rawHodgePosition A P z)⁻¹) (rawHodgeMomentum_holomorphic A P).differentiableOn hi
  apply hp.congr
  intro z hz
  rw [dite_eq_left hz]
  rfl

end

end OAI.RepresentationTheory.Theta.Adelic.PeriodHolomorphic
