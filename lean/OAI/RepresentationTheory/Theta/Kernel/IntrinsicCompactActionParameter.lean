import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear

/-! # Intrinsic Compact Action Parameter -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic

noncomputable section

/-! Actual compact multiplicity operators are explicit continuous
parameters in the ambient analytic frame charts. Their action on the
reference graph is exactly the native moved Hodge frame. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactOne.IntrinsicMultiplicityPhase OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterLinear.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable (A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K)

def actionParameter (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A :=
  fun v => ((p.change v).val,(p.change v).invᵀ)

theorem action_parameter_continuous : Continuous (actionParameter A) := by
  apply continuous_pi
  intro v
  have hv : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => p.change v) :=
    (continuous_apply v).comp (IntrinsicCompactProjector.Intrinsic.change_continuous A)
  have hval : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => (p.change v).val) :=
    Units.continuous_val.comp hv
  have hinv : Continuous (fun p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A => (p.change v).inv) :=
    Units.continuous_val.comp hv.inv
  exact hval.prodMk hinv.matrix_transpose

theorem ambient_action_frame (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCompactProjector.IntrinsicParameter.ambientParameter A (actionParameter A p) z.val (Adelic.BallGeometryData.geometricFrame A z a) = IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a := by
  funext v
  by_cases hv : v = A.distinguished
  · calc
      _ = IntrinsicCompactProjector.IntrinsicParameter.ambientParameter A (IntrinsicCompactProjector.IntrinsicParameter.baseParameter A) z.val (Adelic.BallGeometryData.geometricFrame A z a) v := by
        simp only [IntrinsicCompactProjector.IntrinsicParameter.ambientParameter,ite_eq_left hv]
      _ = Adelic.BallGeometryData.geometricFrame A z a v := congrFun (IntrinsicCompactProjector.IntrinsicParameter.ambientParameter_base_frame A z a) v
      _ = IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a v := by
        subst v
        simp [IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,p.distinguished]
  · simp only [IntrinsicCompactProjector.IntrinsicParameter.ambientParameter,ite_eq_right hv,actionParameter,IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame,IntrinsicCompactOne.IntrinsicMultiplicityPhase.compactPhase,
      IntrinsicCompactOne.IntrinsicMultiplicityPhase.multiplicityPhase,Matrix.mulVec,dotProduct]

theorem coordinate_action_frame (B : Adelic.DataTheta.ComparisonData F H K A) (hG : Adelic.DataTheta.GeometryIdentification B)
    (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B (actionParameter A p) z.val).mulVec
      (Sum.elim ((B.frame z).val.mulVec a)
        ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a))) =
      B.complexPhase.symm (IntrinsicCompactOne.IntrinsicMultiplicityPhase.movingFrame A p z a) := by
  rw [IntrinsicParameterLinear.Intrinsic.coordinateProjector_apply,hG.2.2.2.2.2.2.1,ambient_action_frame]

theorem action_parameter_native_frame (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A)
    (B : Adelic.DataTheta.ComparisonData F H K A) (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
    (hG : Adelic.DataTheta.GeometryIdentification B) (hGp : Adelic.DataTheta.GeometryIdentification Bp)
    (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B (actionParameter A p) z.val).mulVec
      (Sum.elim ((B.frame z).val.mulVec a)
        ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a))) =
      (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).symm
        (Sum.elim ((Bp.frame z).val.mulVec a)
          ((Bp.period z).matrix.mulVec ((Bp.frame z).val.mulVec a))) :=
  (coordinate_action_frame A B hG p z a).trans (IntrinsicCompactPhaseChange.Intrinsic.compact_inverse_graph p B Bp hGp z a).symm

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic
