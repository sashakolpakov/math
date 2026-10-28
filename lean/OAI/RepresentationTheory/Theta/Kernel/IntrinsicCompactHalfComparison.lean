import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameRatio
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology

/-! # Intrinsic Compact Half Comparison -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactHalfComparison.Intrinsic

noncomputable section

/-! Actual native half frames for compact choices differ by a single
nonzero constant on the ball. The constant is fixed by their values at
the origin, so no continuous selection of the pointwise witnesses is
assumed. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameRatio.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicBallTopology.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}
variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

def compactHalfRatio (z : Adelic.BallNatural.Ball) : ℂ := Bp.halfFrame z / B.halfFrame z

theorem compact_half_ratio_square (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    compactHalfRatio p B Bp z ^ 2 = (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp).det *
      (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,IntrinsicBallTopology.Intrinsic.origin.val)).det := by
  have hd := congrArg Matrix.det (IntrinsicCompactFrameComparison.Intrinsic.compact_position_frame p B Bp hC hCp hG hGp z)
  have hf : IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B z.val = (B.frame z).val := dite_eq_left z.property
  rw [Matrix.det_mul,IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame,Matrix.det_mul,hf,
    IntrinsicFrameRatio.Intrinsic.action_position_determinant_constant B hC hG p z IntrinsicBallTopology.Intrinsic.origin] at hd
  change (Bp.halfFrame z / B.halfFrame z) ^ 2 = _
  rw [div_pow,(hGp.2.2.2.2.2.1 z).2,(hG.2.2.2.2.2.1 z).2]
  apply (div_eq_iff (isUnit_iff_ne_zero.mp
    ((Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit (B.frame z))))).mpr
  exact hd.symm.trans (mul_assoc _ _ _).symm

theorem compact_half_ratio_constant (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) :
    ∀ z, compactHalfRatio p B Bp z = compactHalfRatio p B Bp IntrinsicBallTopology.Intrinsic.origin := by
  apply IntrinsicBallTopology.Intrinsic.constant_of_square
  · exact (IntrinsicBallTopology.Intrinsic.holomorphic_continuous Bp.halfFrame hGp.2.2.2.2.1).div
      (IntrinsicBallTopology.Intrinsic.holomorphic_continuous B.halfFrame hG.2.2.2.2.1)
      (fun z => (hG.2.2.2.2.2.1 z).1)
  · intro z
    rw [compact_half_ratio_square p B Bp hC hCp hG hGp z,
      compact_half_ratio_square p B Bp hC hCp hG hGp IntrinsicBallTopology.Intrinsic.origin]
  · exact div_ne_zero (hGp.2.2.2.2.2.1 IntrinsicBallTopology.Intrinsic.origin).1 (hG.2.2.2.2.2.1 IntrinsicBallTopology.Intrinsic.origin).1

theorem compact_half_frame_normalized (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    Bp.halfFrame z = (Bp.halfFrame IntrinsicBallTopology.Intrinsic.origin / B.halfFrame IntrinsicBallTopology.Intrinsic.origin) * B.halfFrame z :=
  (div_eq_iff (hG.2.2.2.2.2.1 z).1).mp
    (compact_half_ratio_constant p B Bp hC hCp hG hGp z)

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactHalfComparison.Intrinsic
