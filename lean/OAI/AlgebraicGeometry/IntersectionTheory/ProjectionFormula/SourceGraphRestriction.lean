import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.SmoothPullback
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Chow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.GraphChowValue
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ChowPushforwardComposition

/-! # Source Graph Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceGraphRestriction

noncomputable section

/-! A graph contribution from an open and closed source part is the
embedding of the graph pullback computed on that part. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction

variable {V X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

local instance : SmoothOfRelativeDimension (m + n) (ProductRestriction.presentation P i).space.structureMap :=
  ProductDimension.relativeDimension (ProductRestriction.presentation P i) m n

theorem graph_embedding :
    ProperCycleLinearity.cyclePushforward (P.graph f) 0 n (Clopen.CycleMaps.embed i m 0 (ProperCycleLinearity.fundamentalCycle V)) =
      Clopen.CycleMaps.embed (ProductRestriction.inclusion P i) (m + n) n ((ProductRestriction.presentation P i).graphCycle (i ≫ f) n) := by
  rw [Clopen.CycleMaps.embed_eq_pushforward, ProperCycleLinearity.ProductPresentation.graphCycle, Clopen.CycleMaps.embed_eq_pushforward,
    PushforwardComposition.cycle_comp i (P.graph f) m (m + n) 0 0 n (by omega),
    PushforwardComposition.cycle_comp ((ProductRestriction.presentation P i).graph (i ≫ f)) (ProductRestriction.inclusion P i)
      (m + n) (m + n) 0 n n rfl, ProductRestriction.graph P i rfl]

theorem secondPullback_restrict (a : Y.RationalDimensionCycle 1) :
    Clopen.CycleMaps.restrict (ProductRestriction.inclusion P i) (m + n) 1 (P.secondPullbackCycle 1 a) =
      (ProductRestriction.presentation P i).secondPullbackCycle 1 a := by
  let : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P
  rw [General.ProductDivisorPullback.secondPullback_eq_flatMap P m n,
    General.ProductDivisorPullback.secondPullback_eq_flatMap (ProductRestriction.presentation P i) m n,
    Clopen.SmoothPullback.restrict_flatMap (ProductRestriction.inclusion P i) P.snd (m + n) n,
    ProductRestriction.second P i]

theorem contribution (a : Y.RationalDimensionCycle 1) :
    ChowPushforwardMap.map P.fst (m + n) m (1 + n) 1 (by omega)
      (Divisor.ChowMap.map P.space (m + n) n
        (ProperCycleLinearity.cycleToChowQ P.space 1 (P.secondPullbackCycle 1 a))
        (ProperCycleLinearity.cycleToChowQ P.space n (ProperCycleLinearity.cyclePushforward (P.graph f) 0 n
          (Clopen.CycleMaps.embed i m 0 (ProperCycleLinearity.fundamentalCycle V))))) =
      ChowPushforwardMap.map i m m 1 1 rfl
        (General.DivisorPullback.pull (ProductRestriction.presentation P i) (i ≫ f) m n (ProperCycleLinearity.cycleToChowQ Y 1 a)) := by
  rw [graph_embedding P i f m n,
    Clopen.Chow.divisor (ProductRestriction.inclusion P i) (m + n) n,
    secondPullback_restrict P i m n,
    ChowPushforwardComposition.comp (ProductRestriction.inclusion P i) P.fst (m + n) (m + n) m
      (1 + n) (1 + n) 1 rfl (by omega) (by omega), ProductRestriction.first P i,
    Divisor.GraphChowValue.value (ProductRestriction.presentation P i) (i ≫ f) m n,
    ChowPushforwardComposition.comp (ProductRestriction.presentation P i).fst i (m + n) m m
      (1 + n) 1 1 (by omega) rfl (by omega)]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceGraphRestriction
