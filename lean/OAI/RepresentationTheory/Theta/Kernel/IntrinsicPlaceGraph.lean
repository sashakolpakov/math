import OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn

/-! # Intrinsic Place Graph -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceGraph.Intrinsic

noncomputable section

/-! The actual native place projection preserves the actual positive
Gaussian graph. The identity follows from the geometric Hodge frame. -/

open scoped _root_.NumberField Classical _root_.Matrix _root_.Matrix.Norms.Elementwise

open OAI.RepresentationTheory.Theta.Adelic.BallNatural OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceProjection.Intrinsic OAI.RepresentationTheory.Theta.Kernel.IntrinsicFrameOn.IntrinsicPlaceProjection OAI.RepresentationTheory.Theta.Kernel.IntrinsicRealComplexification.Intrinsic

variable {F : Type} [Field F] [NumberField F] {d : F}
variable {H : (Matrix (Fin 3) (Fin 3) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {K : (Matrix (Fin 2) (Fin 2) (Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic F d))ˣ}
variable {A : Adelic.BallGeometryData.BallArithmeticData F d 2 H K} (B : Adelic.DataTheta.ComparisonData F H K A)
variable {P : Weil.AdelicSplitting.Assembly.Construction.GlobalFrames F d 3 2 H K}

theorem native_place_graph (hC : Adelic.DataTheta.CoordinateIdentification B P) (hG : Adelic.DataTheta.GeometryIdentification B)
    (v : Fin A.places) (z : Adelic.BallNatural.Ball) (q : Adelic.BallGeometryData.FrameIndex A → ℂ) :
    IntrinsicRealComplexification.Intrinsic.complexifiedLinear (IntrinsicPlaceProjection.Intrinsic.realPlaceProjection B v) (Sum.elim q ((B.period z).matrix.mulVec q)) =
      Sum.elim ((IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v).mulVec q)
        ((B.period z).matrix.mulVec ((IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v).mulVec q)) := by
  let a := (B.frame z).inv.mulVec q
  have hqa : (B.frame z).val.mulVec a = q := by
    change (B.frame z).val.mulVec ((B.frame z).inv.mulVec q) = q
    rw [Matrix.mulVec_mulVec,(B.frame z).val_inv,Matrix.one_mulVec]
  have hinput := hG.2.2.2.2.2.2.1 z a
  rw [hqa] at hinput
  have hpos : (B.frame z).val.mulVec ((IntrinsicFrameOn.IntrinsicPlaceProjection.framePlaceMatrix A v).mulVec a) =
      (IntrinsicFrameOn.IntrinsicPlaceProjection.positionPlaceMatrix B v).mulVec q := by
    rw [Matrix.mulVec_mulVec,← IntrinsicFrameOn.IntrinsicPlaceProjection.native_frame_place B hC hG v z,← Matrix.mulVec_mulVec,hqa]
  have houtput := hG.2.2.2.2.2.2.1 z ((IntrinsicFrameOn.IntrinsicPlaceProjection.framePlaceMatrix A v).mulVec a)
  rw [hpos] at houtput
  apply B.complexPhase.injective
  rw [IntrinsicPlaceProjection.Intrinsic.complex_place_projection B hC,hinput,IntrinsicFrameOn.IntrinsicPlaceProjection.geometric_frame_place,houtput]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicPlaceGraph.Intrinsic
