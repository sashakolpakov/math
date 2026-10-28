import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices

/-! # Intrinsic Compact Real Phase -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase.Intrinsic

noncomputable section

/-! The compact phase change is real, with the same rational and real
position matrices. This is the compatibility needed for the Gaussian's
imaginary form and its completion. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicCoordinateAgreement OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicPositionMatrices.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

def compactRealPhaseChange : ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) ≃L[ℝ]
    ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) :=
  B.realPhase.symm.trans Bp.realPhase

def compactRealPositionMatrix : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℝ :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp)

def compactRealPositionInverse : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℝ :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp).symm

theorem compact_real_position_inverse :
    compactRealPositionInverse p B Bp * compactRealPositionMatrix p B Bp = 1 :=
  IntrinsicPositionMatrices.Intrinsic.scalarMatrix_inverse (IntrinsicCompactPhaseChange.Intrinsic.compactRationalPositionChange p B Bp).symm

theorem compact_position_matrix_real :
    IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp = (compactRealPositionMatrix p B Bp).map Complex.ofRealHom := by
  ext i j
  exact (Complex.ofReal_ratCast _).symm

theorem compact_position_ofReal (x : Adelic.BallGeometryData.FrameIndex A → ℝ) :
    (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp).mulVec (fun i => (x i : ℂ)) =
      fun i => ((compactRealPositionMatrix p B Bp).mulVec x i : ℂ) := by
  rw [compact_position_matrix_real]
  funext i
  exact (RingHom.map_mulVec Complex.ofRealHom (compactRealPositionMatrix p B Bp) x i).symm

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_phase_change_real (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℝ) :
    IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp (fun i => (x i : ℂ)) =
      fun i => (compactRealPhaseChange p B Bp x i : ℂ) := by
  let u := B.realPhase.symm x
  have h := IntrinsicCompactOne.IntrinsicCoordinateAgreement.compact_comparison_real p B Bp hC hCp u
  have hx : (fun i => (B.realPhase u i : ℂ)) = fun i => (x i : ℂ) :=
    congrArg (fun y => fun i => (y i : ℂ)) (B.realPhase.apply_symm_apply x)
  have he := h.trans (congrArg (fun y => IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhaseInverse A p (B.complexPhase y)) hx)
  exact (congrArg Bp.complexPhase.symm he.symm).trans (Bp.complexPhase.symm_apply_apply _)

theorem compact_position_real (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : Adelic.BallGeometryData.FrameIndex A → ℝ) :
    IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp (fun i => (x i : ℂ)) =
      fun i => ((compactRealPositionMatrix p B Bp).mulVec x i : ℂ) :=
  (IntrinsicCompactPositionMatrices.Intrinsic.compact_position_matrix_apply p B Bp hC hCp _).symm.trans (compact_position_ofReal p B Bp x)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactRealPhase.Intrinsic
