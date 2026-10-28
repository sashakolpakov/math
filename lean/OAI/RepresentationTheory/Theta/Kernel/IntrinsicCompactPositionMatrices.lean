import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices

/-! # Intrinsic Compact Position Matrices -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic

noncomputable section

/-! Actual rational position matrices and their inverses for the
compact-coordinate comparison. Their complex action is derived from
the native coordinate identifications. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic

theorem scalar_matrix_apply_rational {I J k : Type} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] [Field k] [CharZero k]
    (e : (I → ℚ) ≃ₗ[ℚ] (J → ℚ)) (q : I → ℚ) :
    (IntrinsicPositionMatrices.Intrinsic.scalarMatrix (k := k) e).mulVec (fun i => (q i : k)) = fun j => (e q j : k) := by
  funext i
  change (∑ j, ((LinearMap.toMatrix' e.toLinearMap i j : ℚ) : k) * (q j : k)) = (e q i : k)
  calc
    _ = ((∑ j, LinearMap.toMatrix' e.toLinearMap i j * q j : ℚ) : k) := by
      simp only [Rat.cast_sum,Rat.cast_mul]
    _ = _ := congrArg (fun r : ℚ => (r : k)) (congrFun (LinearMap.toMatrix'_mulVec e.toLinearMap q) i)

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

def compactPositionMatrix : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp)

def compactPositionInverse : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp).symm

theorem compact_position_matrix_inverse :
    compactPositionMatrix p B Bp * compactPositionInverse p B Bp = 1 :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix_inverse (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp)

theorem compact_position_inverse_matrix :
    compactPositionInverse p B Bp * compactPositionMatrix p B Bp = 1 :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix_inverse (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp).symm

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_position_rational (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (q : Adelic.BallGeometryData.FrameIndex A → ℚ) :
    IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp (fun i => (q i : ℂ)) =
      fun i => (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp q i : ℂ) := by
  have h := IntrinsicCompactPhaseChange.Intrinsic.compact_phase_change_rational p B Bp hC hCp (Sum.elim q 0)
  have hc : (fun i => ((Sum.elim q (0 : Adelic.BallGeometryData.FrameIndex A → ℚ)) i : ℂ)) =
      Sum.elim (fun i => (q i : ℂ)) (0 : Adelic.BallGeometryData.FrameIndex A → ℂ) := by
    funext i
    cases i <;> simp only [Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,Rat.cast_zero]
  rw [hc] at h
  funext i
  have hi := congrFun h (.inl i)
  rw [IntrinsicCompactPhaseChange.Intrinsic.compact_rational_position p B Bp hC hCp] at hi
  exact hi

theorem compact_position_matrix_linear (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) :
    Matrix.toLin' (compactPositionMatrix p B Bp) = IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp := by
  apply IntrinsicCoordinateAgreement.IntrinsicPositionTransport.complexLinear_ext_rational
  intro q
  exact (scalar_matrix_apply_rational (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp) q).trans
    (compact_position_rational p B Bp hC hCp q).symm

theorem compact_position_matrix_apply (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (compactPositionMatrix p B Bp).mulVec x = IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp x :=
  congrArg (fun L => L x) (compact_position_matrix_linear p B Bp hC hCp)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic
