import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Smooth.SectionChow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ChowUnit
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ClosedGeometricIntegral
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductDimension

/-! # Fiber Graph Section -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberGraphSection

noncomputable section

/-! The graph-section identity needs only integral fibers of the first
projection. Its source may have several connected components. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity

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

theorem chow (p : ℕ) (b : X.RationalDimensionCycle p) :
    General.GeneralChowIntersection.chowMap P.space (m + n) p n
      (ProperCycleLinearity.cycleToChowQ P.space p (ProjectionFormula.Smooth.Cycle.flatMap P.fst p b))
      (ProperCycleLinearity.cycleToChowQ P.space n (P.graphCycle f n)) =
    ChowPushforwardMap.map (P.graph f) m (m + n) p (p + n) (by omega) (ProperCycleLinearity.cycleToChowQ X p b) := by
  have aux (t : ℕ) (ht : 0 + n = t) :
      General.GeneralChowIntersection.chowMap P.space (m + n) p t
        (ProperCycleLinearity.cycleToChowQ P.space p (ProjectionFormula.Smooth.Cycle.flatMap P.fst p b))
        (ChowPushforwardMap.map (P.graph f) m (m + n) 0 t (by omega)
          (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X))) =
      ChowPushforwardMap.map (P.graph f) m (m + n) p (p + t) (by omega)
        (General.GeneralChowIntersection.chowMap X m p 0 (ProperCycleLinearity.cycleToChowQ X p b)
          (ProperCycleLinearity.cycleToChowQ X 0 (ProperCycleLinearity.fundamentalCycle X))) := by
    subst t
    exact ProjectionFormula.Smooth.SectionChow.chow (P.graph f) P.fst (P.graph_fst f)
      (m + n) m n rfl p 0 b (ProperCycleLinearity.fundamentalCycle X)
  have h := aux n (Nat.zero_add n)
  rw [General.ChowUnit.right, ChowPushforwardMap.map_mk] at h
  exact h

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Integral.FiberGraphSection
