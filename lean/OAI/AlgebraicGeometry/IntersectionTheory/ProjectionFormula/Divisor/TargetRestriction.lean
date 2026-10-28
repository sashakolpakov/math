import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.SmoothTarget
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceGraphRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Chow

/-! # Target Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.TargetRestriction

noncomputable section

/-! The exact divisor graph pullback through an open and closed target
part agrees with graph pullback of the restricted divisor Chow class. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction.Target

variable {X V Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (i : V.toOver ⟶ Y.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
  (f : X.toOver ⟶ V.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n V.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

local instance : SmoothOfRelativeDimension (m + n) (ProductRestriction.Target.presentation P i).space.structureMap :=
  ProductDimension.relativeDimension (ProductRestriction.Target.presentation P i) m n

theorem graph_embedding :
    P.graphCycle (f ≫ i) n = Clopen.CycleMaps.embed (ProductRestriction.Target.inclusion P i) (m + n) n ((ProductRestriction.Target.presentation P i).graphCycle f n) := by
  rw [ProperCycleLinearity.ProductPresentation.graphCycle, ProperCycleLinearity.ProductPresentation.graphCycle, Clopen.CycleMaps.embed_eq_pushforward,
    PushforwardComposition.cycle_comp ((ProductRestriction.Target.presentation P i).graph f) (ProductRestriction.Target.inclusion P i)
      (m + n) (m + n) 0 n n rfl, ProductRestriction.Target.graph P i rfl]

theorem secondPullback_restrict (a : Y.RationalDimensionCycle 1) :
    Clopen.CycleMaps.restrict (ProductRestriction.Target.inclusion P i) (m + n) 1 (P.secondPullbackCycle 1 a) =
      (ProductRestriction.Target.presentation P i).secondPullbackCycle 1 (Clopen.CycleMaps.restrict i n 1 a) := by
  let : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P
  let : Smooth (ProductRestriction.Target.presentation P i).snd.left := ProductDivisorPullback.snd_smooth (ProductRestriction.Target.presentation P i)
  rw [General.ProductDivisorPullback.secondPullback_eq_flatMap P m n,
    General.ProductDivisorPullback.secondPullback_eq_flatMap (ProductRestriction.Target.presentation P i) m n,
    Clopen.SmoothPullback.restrict_flatMap (ProductRestriction.Target.inclusion P i) P.snd (m + n) n,
    ProductRestriction.Target.second P i, Clopen.SmoothTarget.factor i (ProductRestriction.Target.presentation P i).snd (m + n) n]

theorem pull (a : ProperCycleLinearity.ChowQ Y 1) :
    General.DivisorPullback.pull P (f ≫ i) m n a =
      General.DivisorPullback.pull (ProductRestriction.Target.presentation P i) f m n
        (Clopen.Chow.DivisorRestriction.map i n a) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y 1 a
  rw [Clopen.Chow.DivisorRestriction.map_mk, GraphChowValue.value P (f ≫ i) m n,
    graph_embedding P i f m n, Clopen.Chow.divisor (ProductRestriction.Target.inclusion P i) (m + n) n,
    secondPullback_restrict P i m n,
    ChowPushforwardComposition.comp (ProductRestriction.Target.inclusion P i) P.fst (m + n) (m + n) m
      (1 + n) (1 + n) 1 rfl (by omega) (by omega), ProductRestriction.Target.first P i,
    GraphChowValue.value (ProductRestriction.Target.presentation P i) f m n]

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.TargetRestriction
