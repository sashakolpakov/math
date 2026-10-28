import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.SourceGraphRestriction
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.ComponentMaps

/-! # Pullback Component Sum -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PullbackComponentSum

noncomputable section

/-! The exact divisor graph pullback is the sum of the embedded graph
pullbacks on the actual integral components of its source. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProductRestriction

variable {X Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (m n : ℕ)
  [SmoothOfRelativeDimension m X.structureMap] [SmoothOfRelativeDimension n Y.structureMap]

local instance : SmoothOfRelativeDimension (m + n) P.space.structureMap :=
  ProductDimension.relativeDimension P m n

local instance component_dimension (C : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C

theorem sum [Fintype (irreducibleComponents X.carrier)] (a : ProperCycleLinearity.ChowQ Y 1) :
    General.DivisorPullback.pull P f m n a =
      ∑ C : irreducibleComponents X.carrier,
        ChowPushforwardMap.map (Component.Image.inclusion X C) m m 1 1 rfl
          (General.DivisorPullback.pull (ProductRestriction.presentation P (Component.Image.inclusion X C))
            (Component.Image.inclusion X C ≫ f) m n a) := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective Y 1 a
  rw [GraphChowValue.value P f m n, ProperCycleLinearity.ProductPresentation.graphCycle,
    ← Clopen.ComponentMaps.sum_fundamental X m]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro C _
  exact SourceGraphRestriction.contribution P (Component.Image.inclusion X C) f m n a

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PullbackComponentSum
