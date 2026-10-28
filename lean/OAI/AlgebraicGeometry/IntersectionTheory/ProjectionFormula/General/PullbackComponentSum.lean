import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceGraphRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ClopenChow
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.GraphChowValue

/-! # Pullback Component Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackComponentSum

noncomputable section

section

/-! Graph pullback contributions from an open and closed source part
commute with native embedding, in all codimensions. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace SourceGraphRestriction

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction

variable {V X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (i : V.toOver ⟶ X.toOver) [IsOpenImmersion i.left] [IsClosedImmersion i.left]
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m V.structureMap] [SmoothOfRelativeDimension m X.structureMap]
  [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap := ProductDimension.relativeDimension P m n

local instance : SmoothOfRelativeDimension (m + n) (ProductRestriction.presentation P i).space.structureMap :=
  ProductDimension.relativeDimension (ProductRestriction.presentation P i) m n

theorem secondPullback_restrict (p : ℕ) (a : Y.RationalDimensionCycle p) :
    Clopen.CycleMaps.restrict (ProductRestriction.inclusion P i) (m + n) p (P.secondPullbackCycle p a) =
      (ProductRestriction.presentation P i).secondPullbackCycle p a := by
  let : Smooth P.snd.left := ProductDivisorPullback.snd_smooth P
  rw [ProductPullback.secondPullback_eq_flatMap P m n p,
    ProductPullback.secondPullback_eq_flatMap (ProductRestriction.presentation P i) m n p,
    ClopenCycles.restrict_flatMap (ProductRestriction.inclusion P i) P.snd (m + n) n p,
    ProductRestriction.second P i]

theorem contribution (p : ℕ) (a : Y.RationalDimensionCycle p) :
    ChowPushforwardMap.map P.fst (m + n) m (p + n) p (by omega)
      (GeneralChowIntersection.chowMap P.space (m + n) p n
        (ProperCycleLinearity.cycleToChowQ P.space p (P.secondPullbackCycle p a))
        (ProperCycleLinearity.cycleToChowQ P.space n (ProperCycleLinearity.cyclePushforward (P.graph f) 0 n
          (Clopen.CycleMaps.embed i m 0 (ProperCycleLinearity.fundamentalCycle V))))) =
      ChowPushforwardMap.map i m m p p rfl
        (ChowPullback.pull (ProductRestriction.presentation P i) (i ≫ f) m n p (ProperCycleLinearity.cycleToChowQ Y p a)) := by
  rw [SourceGraphRestriction.graph_embedding P i f m n,
    ClopenChow.cycle_intersection (ProductRestriction.inclusion P i) (m + n) p n,
    secondPullback_restrict P i m n p,
    ChowPushforwardComposition.comp (ProductRestriction.inclusion P i) P.fst (m + n) (m + n) m
      (p + n) (p + n) p rfl (by omega) (by omega), ProductRestriction.first P i,
    GraphChowValue.value (ProductRestriction.presentation P i) (i ≫ f) m n p,
    ChowPushforwardComposition.comp (ProductRestriction.presentation P i).fst i (m + n) m m
      (p + n) p p (by omega) rfl (by omega)]

end SourceGraphRestriction

end

/-! The exact graph pullback is the sum of its contributions from
the actual integral source components in every degree. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap := ProductDimension.relativeDimension P m n

local instance component_dimension (C : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C

theorem sum [Fintype (irreducibleComponents X.carrier)] (p : ℕ) (a : ProperCycleLinearity.ChowQ Y p) :
    ChowPullback.pull P f m n p a =
      ∑ C : irreducibleComponents X.carrier,
        ChowPushforwardMap.map (Component.Image.inclusion X C) m m p p rfl
          (ChowPullback.pull (ProductRestriction.presentation P (Component.Image.inclusion X C))
            (Component.Image.inclusion X C ≫ f) m n p a) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y p a
  rw [GraphChowValue.value P f m n p, ProperCycleLinearity.ProductPresentation.graphCycle,
    ← Clopen.ComponentMaps.sum_fundamental X m]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro C _
  exact SourceGraphRestriction.contribution P (Component.Image.inclusion X C) f m n p a

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackComponentSum
