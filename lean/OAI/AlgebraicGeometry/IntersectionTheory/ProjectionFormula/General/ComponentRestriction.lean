import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.PullbackComponentSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ComponentRestriction

/-! # Component Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ComponentRestriction

noncomputable section

/-! Restriction of the exact graph pullback to a source component
is the graph pullback for its restricted product presentation. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

local instance component_dimension (C : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C

theorem map_push_other (C D : irreducibleComponents X.carrier) (hCD : C ≠ D)
    (p : ℕ) (a : ProperCycleLinearity.ChowQ (X.componentVariety D).presentation p) :
    ClopenChow.restrictMap (Component.Image.inclusion X C) m p
      (ChowPushforwardMap.map (Component.Image.inclusion X D) m m p p rfl a) = 0 := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective (X.componentVariety D).presentation p a
  rw [ChowPushforwardMap.map_mk, ClopenChow.restrictMap_mk,
    ← Clopen.CycleMaps.embed_eq_pushforward (Component.Image.inclusion X D) m,
    Divisor.ComponentRestriction.restrict_embed_other X m C D hCD p, map_zero]

variable {X} {Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (n : ℕ) [SmoothOfRelativeDimension n Y.structureMap]

theorem pull (C : irreducibleComponents X.carrier) (p : ℕ) (a : ProperCycleLinearity.ChowQ Y p) :
    ClopenChow.restrictMap (Component.Image.inclusion X C) m p (ChowPullback.pull P f m n p a) =
      ChowPullback.pull (ProductRestriction.presentation P (Component.Image.inclusion X C))
        (Component.Image.inclusion X C ≫ f) m n p a := by
  let := Fintype.ofFinite (irreducibleComponents X.carrier)
  rw [PullbackComponentSum.sum P f m n p, map_sum, Finset.sum_eq_single C]
  · exact ClopenChow.restrictMap_push (Component.Image.inclusion X C) m p _
  · intro D _ hD
    exact map_push_other X m C D (Ne.symm hD) p _
  · simp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.ComponentRestriction
