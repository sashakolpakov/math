import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactLinear

/-! # Intrinsic Compact Phase Change -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic

noncomputable section

/-! The compact-choice physical coordinate change is the
complexification of the actual rational trace-coordinate change. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactLinear.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicCoordinateAgreement

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))

def compactPhaseChange : ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) ≃L[ℂ]
    ((Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p)) → ℂ) :=
  (B.complexPhase.trans (IntrinsicCompactLinear.Intrinsic.compactContinuousEquiv A p).symm).trans Bp.complexPhase.symm

def compactRationalPhaseChange : ((Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℚ) ≃ₗ[ℚ]
    ((Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) ⊕ Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p)) → ℚ) :=
  B.rationalPhase.symm.trans Bp.rationalPhase

def compactRationalPositionChange : (Adelic.BallGeometryData.FrameIndex A → ℚ) ≃ₗ[ℚ]
    (Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) → ℚ) :=
  B.rationalPosition.symm.trans Bp.rationalPosition

theorem compact_phase_change_apply (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℂ) :
    compactPhaseChange p B Bp x =
      Bp.complexPhase.symm (IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhaseInverse A p (B.complexPhase x)) := rfl

variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_phase_change_rational (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℚ) :
    compactPhaseChange p B Bp (fun i => (x i : ℂ)) =
      fun i => (compactRationalPhaseChange p B Bp x i : ℂ) := by
  have h := IntrinsicCompactOne.IntrinsicCoordinateAgreement.compact_comparison_rational p B Bp hC hCp (B.rationalPhase.symm x)
  rw [LinearEquiv.apply_symm_apply] at h
  rw [compact_phase_change_apply,← h,ContinuousLinearEquiv.symm_apply_apply]
  rfl

theorem compact_rational_position (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (x : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℚ)
    (i : Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p)) :
    compactRationalPhaseChange p B Bp x (.inl i) =
      compactRationalPositionChange p B Bp (fun j => x (.inl j)) i := by
  change Bp.rationalPhase (B.rationalPhase.symm x) (.inl i) = _
  rw [hCp.2.1]
  have he : (fun j => B.rationalPhase.symm x (.inl j)) =
      B.rationalPosition.symm (fun j => x (.inl j)) := by
    apply B.rationalPosition.injective
    funext j
    rw [← hC.2.1,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
  rw [he]
  rfl

theorem compact_rational_pairing (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P)
    (x y : (Adelic.BallGeometryData.FrameIndex A ⊕ Adelic.BallGeometryData.FrameIndex A) → ℚ) :
    Adelic.DataTheta.standardPairing (compactRationalPhaseChange p B Bp x) (compactRationalPhaseChange p B Bp y) =
      Adelic.DataTheta.standardPairing x y := by
  change Adelic.DataTheta.standardPairing (Bp.rationalPhase (B.rationalPhase.symm x))
    (Bp.rationalPhase (B.rationalPhase.symm y)) = _
  rw [hCp.2.2.1,← hC.2.2.1,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]

theorem compact_inverse_graph (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball)
    (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (compactPhaseChange p B Bp).symm
      (Sum.elim ((Bp.frame z).val.mulVec a)
        ((Bp.period z).matrix.mulVec ((Bp.frame z).val.mulVec a))) =
      B.complexPhase.symm (IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a) := by
  change B.complexPhase.symm (IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase A p (Bp.complexPhase _)) = _
  exact congrArg (fun w => B.complexPhase.symm (IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase A p w))
    (hGp.2.2.2.2.2.2.1 z a)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic
