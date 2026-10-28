import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter
import OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph

/-! # Intrinsic Compact Frame Comparison -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic

/-! The actual compact-action chart frame differs from the native
chosen frame by its rational position change. In particular its
position block is invertible at every ball point. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPositionMatrices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

theorem parameter_frame_apply (B : Adelic.DataTheta.ComparisonData F H K A) (u : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A)
    (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) (i : Adelic.BallGeometryData.FrameIndex A) :
    (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (u,z.val)).mulVec a i =
      (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val).mulVec
        (Sum.elim ((B.frame z).val.mulVec a)
          ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a))) (.inl i) := by
  change ((IntrinsicGraphCalculus.Intrinsic.positionBlock (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (IntrinsicParameterGraph.Intrinsic.periodExtension B z.val)) *
    IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B z.val).mulVec a i = _
  rw [IntrinsicParameterGraph.Intrinsic.periodExtension_ball,show IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B z.val = (B.frame z).val from dite_eq_left z.property,
    ← Matrix.mulVec_mulVec,IntrinsicGraphCalculus.Intrinsic.positionBlock_apply]

variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem compact_position_frame (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp * IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) = (Bp.frame z).val := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro a
  let q := (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p) z.val).mulVec
    (Sum.elim ((B.frame z).val.mulVec a) ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a)))
  have hq : IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _ q = (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a := by
    funext i
    exact (parameter_frame_apply B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p) z a i).symm
  have hE : IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp q = Sum.elim ((Bp.frame z).val.mulVec a)
      ((Bp.period z).matrix.mulVec ((Bp.frame z).val.mulVec a)) :=
    (congrArg (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp)
      (IntrinsicCompactActionParameter.Intrinsic.action_parameter_native_frame A p B Bp hG hGp z a)).trans
        ((IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).apply_symm_apply _)
  change (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp * IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a = _
  exact (Matrix.mulVec_mulVec a (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)
    (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).symm.trans
      ((IntrinsicCompactPositionMatrices.Intrinsic.compact_position_matrix_apply p B Bp hC hCp _).trans
        ((congrArg (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp) hq.symm).trans
          ((IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_positions p B Bp hC hCp q).symm.trans
            (congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ _) hE))))

theorem compact_frame_det_nonzero (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).det ≠ 0 := by
  have hRF := compact_position_frame p B Bp hC hCp hG hGp z
  have hi : Function.Injective (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec := by
    intro x y hxy
    have hx := (Matrix.mulVec_mulVec x (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)
      (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).trans (congrArg (fun M => M.mulVec x) hRF)
    have hy := (Matrix.mulVec_mulVec y (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp)
      (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val))).trans (congrArg (fun M => M.mulVec y) hRF)
    exact (Matrix.mulVec_injective_of_isUnit (Units.isUnit (Bp.frame z)))
      (hx.symm.trans ((congrArg (IntrinsicCompactPositionMatrices.Intrinsic.compactPositionMatrix p B Bp).mulVec hxy).trans hy))
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_injective_iff_isUnit.mp hi))

theorem action_parameter_graph_domain (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) :
    (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val) ∈ IntrinsicParameterGraph.Intrinsic.parameterGraphDomain B := by
  refine ⟨z.property,?_⟩
  have h := compact_frame_det_nonzero p B Bp hC hCp hG hGp z
  have hm : (IntrinsicParameterGraph.Intrinsic.parameterPositionBlock B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).det * (IntrinsicParameterGraph.IntrinsicHalfFrame.frameExtension B z.val).det ≠ 0 := by
    simpa only [IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame,Matrix.det_mul] using h
  exact (mul_ne_zero_iff.mp hm).1

end RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic

namespace RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.IntrinsicGraph

/-! The compact-action chart period and the actual native period have
the same graph after the rational symplectic coordinate change. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactChoices.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactPhaseChange.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactSymplecticTransport.Intrinsic
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactActionParameter.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicCoordinateAgreement.IntrinsicPositionTransport
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicCompactProjector.IntrinsicParameter OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicParameterGraph.IntrinsicHalfFrame
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicGraphCalculus.Intrinsic

theorem graphChart_graph {I : Type} [Fintype I] [DecidableEq I]
    (Q : Matrix (I ⊕ I) (I ⊕ I) ℂ) (Z : Matrix I I ℂ)
    (hL : IsUnit (IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z).det) (x : I → ℂ) :
    Q.mulVec (Sum.elim x (Z.mulVec x)) =
      Sum.elim ((IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z).mulVec x)
        ((IntrinsicGraphCalculus.Intrinsic.graphChart Q Z).mulVec ((IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z).mulVec x)) := by
  have hi : (IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z)⁻¹.mulVec ((IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z).mulVec x) = x := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ hL,Matrix.one_mulVec]
  have he : (IntrinsicGraphCalculus.Intrinsic.graphChart Q Z).mulVec ((IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z).mulVec x) = (IntrinsicGraphCalculus.Intrinsic.momentumBlock Q Z).mulVec x :=
    (Matrix.mulVec_mulVec ((IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z).mulVec x) (IntrinsicGraphCalculus.Intrinsic.momentumBlock Q Z)
      (IntrinsicGraphCalculus.Intrinsic.positionBlock Q Z)⁻¹).symm.trans (congrArg (IntrinsicGraphCalculus.Intrinsic.momentumBlock Q Z).mulVec hi)
  funext i
  cases i with
  | inl i => exact (IntrinsicGraphCalculus.Intrinsic.positionBlock_apply Q Z x i).symm
  | inr i => exact (IntrinsicGraphCalculus.Intrinsic.momentumBlock_apply Q Z x i).symm.trans (congrFun he i).symm

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K}

theorem parameter_chart_graph (B : Adelic.DataTheta.ComparisonData F H K A) (u : IntrinsicCompactProjector.IntrinsicParameter.ProjectorParameters A)
    (z : Adelic.BallNatural.Ball) (hu : (u,z.val) ∈ IntrinsicParameterGraph.Intrinsic.parameterGraphDomain B) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val).mulVec
      (Sum.elim ((B.frame z).val.mulVec a) ((B.period z).matrix.mulVec ((B.frame z).val.mulVec a))) =
      Sum.elim ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (u,z.val)).mulVec a)
        ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (u,z.val)).mulVec ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (u,z.val)).mulVec a)) := by
  have hdet : IsUnit (IntrinsicGraphCalculus.Intrinsic.positionBlock (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (B.period z).matrix).det := by
    apply isUnit_iff_ne_zero.mpr
    simpa only [IntrinsicParameterGraph.Intrinsic.parameterPositionBlock,IntrinsicParameterGraph.Intrinsic.periodExtension_ball] using hu.2
  have hf : (IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (u,z.val)).mulVec a =
      (IntrinsicGraphCalculus.Intrinsic.positionBlock (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (B.period z).matrix).mulVec ((B.frame z).val.mulVec a) := by
    funext i
    exact (Intrinsic.parameter_frame_apply B u z a i).trans
      (IntrinsicGraphCalculus.Intrinsic.positionBlock_apply (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (B.period z).matrix ((B.frame z).val.mulVec a) i).symm
  have hZ : IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (u,z.val) =
      IntrinsicGraphCalculus.Intrinsic.graphChart (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (B.period z).matrix := by
    unfold IntrinsicParameterGraph.Intrinsic.parameterPeriodChart
    rw [IntrinsicParameterGraph.Intrinsic.periodExtension_ball]
  rw [hZ]
  exact (graphChart_graph (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (B.period z).matrix hdet ((B.frame z).val.mulVec a)).trans
    (congrArg (fun x => Sum.elim x ((IntrinsicGraphCalculus.Intrinsic.graphChart (IntrinsicCompactProjector.IntrinsicParameter.coordinateProjector A B u z.val) (B.period z).matrix).mulVec x)) hf.symm)

variable (p : IntrinsicCompactChoices.Intrinsic.CompactFrameChoice A) (B : Adelic.DataTheta.ComparisonData F H K A)
variable (Bp : Adelic.DataTheta.ComparisonData F H K (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem native_parameter_graph_frame (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (a : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp
      (Sum.elim ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a)
        ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec
          ((IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec a))) =
      Sum.elim ((Bp.frame z).val.mulVec a) ((Bp.period z).matrix.mulVec ((Bp.frame z).val.mulVec a)) := by
  have h := parameter_chart_graph B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p) z
    (Intrinsic.action_parameter_graph_domain p B Bp hC hCp hG hGp z) a
  exact (congrArg (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp) h.symm).trans
    ((congrArg (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp) (IntrinsicCompactActionParameter.Intrinsic.action_parameter_native_frame A p B Bp hG hGp z a)).trans
      ((IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp).apply_symm_apply _))

theorem compact_graph_in_positions (hC : Adelic.DataTheta.CoordinateIdentification B P)
    (hCp : Adelic.DataTheta.CoordinateIdentification Bp P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (hGp : Adelic.DataTheta.GeometryIdentification Bp) (z : Adelic.BallNatural.Ball) (x : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp
      (Sum.elim x ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec x)) =
      Sum.elim (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp x) ((Bp.period z).matrix.mulVec (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp x)) := by
  let D : Matrix (Adelic.BallGeometryData.FrameIndex A) (Adelic.BallGeometryData.FrameIndex A) ℂ := IntrinsicParameterGraph.IntrinsicHalfFrame.parameterFrame B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)
  let a : Adelic.BallGeometryData.FrameIndex A → ℂ := D⁻¹.mulVec x
  have ha : D.mulVec a = x := by
    change D.mulVec (D⁻¹.mulVec x) = x
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv D
      (isUnit_iff_ne_zero.mpr (Intrinsic.compact_frame_det_nonzero p B Bp hC hCp hG hGp z)),Matrix.one_mulVec]
  have h := native_parameter_graph_frame p B Bp hC hCp hG hGp z a
  have hpos := congrArg (IntrinsicCoordinateAgreement.IntrinsicPositionTransport.positions ℂ (Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p))) h
  have hR : IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp x = (Bp.frame z).val.mulVec a :=
    (congrArg (IntrinsicCompactSymplecticTransport.Intrinsic.compactPositionLinear p B Bp) ha.symm).trans
      ((IntrinsicCompactSymplecticTransport.Intrinsic.compact_phase_positions p B Bp hC hCp
        (Sum.elim (D.mulVec a) ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec (D.mulVec a)))).symm.trans hpos)
  have hs := congrArg (fun y : Adelic.BallGeometryData.FrameIndex A → ℂ =>
    Sum.elim y ((IntrinsicParameterGraph.Intrinsic.parameterPeriodChart B (IntrinsicCompactActionParameter.Intrinsic.actionParameter A p,z.val)).mulVec y)) ha
  exact (congrArg (IntrinsicCompactPhaseChange.Intrinsic.compactPhaseChange p B Bp) hs).symm.trans
    (h.trans (congrArg (fun y : Adelic.BallGeometryData.FrameIndex (IntrinsicCompactChoices.Intrinsic.choiceArithmetic A p) → ℂ =>
      Sum.elim y ((Bp.period z).matrix.mulVec y)) hR.symm))

end RepresentationTheory.Theta.Kernel.IntrinsicCompactFrameComparison.IntrinsicGraph

end

end OAI
