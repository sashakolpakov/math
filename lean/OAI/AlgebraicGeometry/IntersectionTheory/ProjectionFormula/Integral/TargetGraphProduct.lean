import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.GraphPullbackReconstruction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberGraphSection
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowInnerSwap

/-! # Target Graph Product -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.TargetGraphProduct

noncomputable section

/-! For an integral target, graph pushforward identifies the product
with a pulled-back class with intersection on the ambient product. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GeneralChowIntersection OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardMap

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} [IsIntegral Y.carrier]
  (P : ProperCycleLinearity.ProductPresentation X Y) (f : X.toOver ⟶ Y.toOver)
  (m n : ℕ) [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

local instance : Smooth P.fst.left := by
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk P.fst P.snd) P.isLimit).flip
    (inferInstance : Smooth Y.structureMap)

local instance : GeometricallyIntegral (show P.space.carrier ⟶ X.carrier from P.fst.left) := by
  let : GeometricallyIntegral Y.structureMap :=
    ClosedGeometricIntegral.geometricallyIntegral Y.structureMap
  exact MorphismProperty.of_isPullback
    (Over.isPullback_of_binaryFan_isLimit (BinaryFan.mk P.fst P.snd) P.isLimit).flip
    (inferInstance : GeometricallyIntegral Y.structureMap)

omit [IsIntegral Y.carrier] in
theorem graph_pull (p : ℕ) (a : Y.RationalDimensionCycle p) :
    ChowPushforwardMap.map (P.graph f) m (m + n) p (p + n) (by omega)
      (General.ChowPullback.pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a)) =
    General.GeneralChowIntersection.chowMap P.space (m + n) p n (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a))
      (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)) := by
  have h := congrArg (DegreeCast.chow P.space (Nat.add_comm n p))
    (GraphPullbackReconstruction.graph_push_pull P f m n p a)
  rw [ChowPushforwardCast.target, General.ChowAssociativity.comm] at h
  exact h

theorem product (p q : ℕ) (a : Y.RationalDimensionCycle p) (b : X.RationalDimensionCycle q) :
    ChowPushforwardMap.map (P.graph f) m (m + n) (p + q) (p + (q + n)) (by omega)
      (General.GeneralChowIntersection.chowMap X m p q (General.ChowPullback.pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a))
        (ProperCycleLinearity.cycleToChowQ X q b)) =
    General.GeneralChowIntersection.chowMap P.space (m + n) p (q + n) (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a))
      (ChowPushforwardMap.map (P.graph f) m (m + n) q (q + n) (by omega) (ProperCycleLinearity.cycleToChowQ X q b)) := by
  let α := General.ChowPullback.pull P f m n p (ProperCycleLinearity.cycleToChowQ Y p a)
  let β := ProperCycleLinearity.cycleToChowQ X q b
  let A := ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a)
  let B := ProperCycleLinearity.cycleToChowQ P.space q (ProjectionFormula.Smooth.Cycle.flatMap P.fst q b)
  let G := ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)
  obtain ⟨d, hd⟩ := ProperCycleLinearity.cycleToChowQ_surjective X p α
  have hs : General.GeneralChowIntersection.chowMap P.space (m + n) q (p + n) B
      (ChowPushforwardMap.map (P.graph f) m (m + n) p (p + n) (by omega) α) =
      ChowPushforwardMap.map (P.graph f) m (m + n) (q + p) (q + (p + n)) (by omega) (General.GeneralChowIntersection.chowMap X m q p β α) := by
    have h := ProjectionFormula.Smooth.SectionChow.chow (P.graph f) P.fst (P.graph_fst f)
      (m + n) m n rfl q p b d
    rw [hd] at h
    exact h
  have hg : ChowPushforwardMap.map (P.graph f) m (m + n) p (p + n) (by omega) α = General.GeneralChowIntersection.chowMap P.space (m + n) p n A G :=
    graph_pull P f m n p a
  have hb : General.GeneralChowIntersection.chowMap P.space (m + n) q n B G =
      ChowPushforwardMap.map (P.graph f) m (m + n) q (q + n) (by omega) β := FiberGraphSection.chow P f m n q b
  let e : q + (p + n) = p + (q + n) := by omega
  calc
    _ = ChowPushforwardMap.map (P.graph f) m (m + n) (p + q) (p + (q + n)) (by omega)
        (DegreeCast.chow X (Nat.add_comm q p) (General.GeneralChowIntersection.chowMap X m q p β α)) := by
      rw [General.ChowAssociativity.comm]
    _ = ChowPushforwardMap.map (P.graph f) m (m + n) (q + p) (p + (q + n)) (by omega) (General.GeneralChowIntersection.chowMap X m q p β α) :=
      ChowPushforwardCast.source (P.graph f) m (m + n) (q + p) (p + q) (p + (q + n))
        (Nat.add_comm q p) (by omega) (by omega) _
    _ = DegreeCast.chow P.space e
        (ChowPushforwardMap.map (P.graph f) m (m + n) (q + p) (q + (p + n)) (by omega) (General.GeneralChowIntersection.chowMap X m q p β α)) :=
      (ChowPushforwardCast.target (P.graph f) m (m + n) (q + p) (q + (p + n)) (p + (q + n))
        e (by omega) (by omega) _).symm
    _ = DegreeCast.chow P.space e
        (General.GeneralChowIntersection.chowMap P.space (m + n) q (p + n) B (General.GeneralChowIntersection.chowMap P.space (m + n) p n A G)) := by rw [← hs, hg]
    _ = _ := by rw [ChowInnerSwap.swap, hb]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.TargetGraphProduct
