import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.TargetRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenTarget
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenChow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GraphChowValue

/-! # Target Graph Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.TargetGraphRestriction

noncomputable section

/-! Exact graph pullback through an open and closed target part
agrees with pullback of the restricted Chow class in every degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction.Target

variable {X V Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (i : V.toOver ⟶ Y.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
  (f : X.toOver ⟶ V.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n V.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap := ProductDimension.relativeDimension P m n

local instance : SmoothOfRelativeDimension (m + n) (ProductRestriction.Target.presentation P i).space.structureMap :=
  ProductDimension.relativeDimension (ProductRestriction.Target.presentation P i) m n

theorem secondPullback_restrict (p : ℕ) (a : Y.RationalDimensionCycle p) :
    Clopen.CycleMaps.restrict (ProductRestriction.Target.inclusion P i) (m + n) p (P.secondPullbackCycle p a) =
      (ProductRestriction.Target.presentation P i).secondPullbackCycle p (Clopen.CycleMaps.restrict i n p a) := by
  let : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P
  let : Smooth (ProductRestriction.Target.presentation P i).snd.left := ProductDivisorPullback.snd_smooth (ProductRestriction.Target.presentation P i)
  rw [ProductPullback.secondPullback_eq_flatMap P m n p,
    ProductPullback.secondPullback_eq_flatMap (ProductRestriction.Target.presentation P i) m n p,
    ClopenCycles.restrict_flatMap (ProductRestriction.Target.inclusion P i) P.snd (m + n) n p,
    ProductRestriction.Target.second P i, ClopenTarget.factor i (ProductRestriction.Target.presentation P i).snd (m + n) n p]

theorem pull (p : ℕ) (a : ProperCycleLinearity.ChowQ Y p) :
    ChowPullback.pull P (f ≫ i) m n p a =
      ChowPullback.pull (ProductRestriction.Target.presentation P i) f m n p (ClopenChow.restrictMap i n p a) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y p a
  rw [ClopenChow.restrictMap_mk, GraphChowValue.value P (f ≫ i) m n p,
    Divisor.TargetRestriction.graph_embedding P i f m n,
    ClopenChow.cycle_intersection (ProductRestriction.Target.inclusion P i) (m + n) p n,
    secondPullback_restrict P i m n p,
    ChowPushforwardComposition.comp (ProductRestriction.Target.inclusion P i) P.fst (m + n) (m + n) m
      (p + n) (p + n) p rfl (by omega) (by omega), ProductRestriction.Target.first P i,
    GraphChowValue.value (ProductRestriction.Target.presentation P i) f m n p]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.TargetGraphRestriction
