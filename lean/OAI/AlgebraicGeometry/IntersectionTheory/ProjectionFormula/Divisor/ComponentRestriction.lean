import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.PullbackComponentSum
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Clopen.Chow

/-! # Component Restriction -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ComponentRestriction

noncomputable section

/-! Restricting the exact divisor graph pullback to a source component
gives the exact graph pullback for the restricted product presentation. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image

variable (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ) [SmoothOfRelativeDimension m X.structureMap]

local instance component_dimension (C : irreducibleComponents X.carrier) :
    SmoothOfRelativeDimension m (X.componentVariety C).structureMap := Component.Image.component_relativeDimension X m C

theorem restrict_embed_other (C D : irreducibleComponents X.carrier) (hCD : C ≠ D)
    (p : ℕ) (a : (X.componentVariety D).presentation.RationalDimensionCycle p) :
    Clopen.CycleMaps.restrict (Component.Image.inclusion X C) m p
      (Clopen.CycleMaps.embed (Component.Image.inclusion X D) m p a) = 0 := by
  rw [Clopen.ComponentMaps.restrict_eq, Clopen.ComponentMaps.embed_eq]
  ext A
  rw [Component.CycleMaps.restrict_apply, Finsupp.zero_apply]
  apply Component.Principal.CycleDecomposition.embed_apply_outside
  intro hD
  have hC := X.supportComponent_eq_of_subset (Component.Image.supportImage X C p A).val C
    (X.componentSupportImage_subset C A.val)
  have hD' := X.supportComponent_eq_of_subset (Component.Image.supportImage X C p A).val D hD
  exact hCD (hC.symm.trans hD')

theorem map_push_other (C D : irreducibleComponents X.carrier) (hCD : C ≠ D)
    (a : ProperCycleLinearity.ChowQ (X.componentVariety D).presentation 1) :
    Clopen.Chow.DivisorRestriction.map (Component.Image.inclusion X C) m
      (ChowPushforwardMap.map (Component.Image.inclusion X D) m m 1 1 rfl a) = 0 := by
  obtain ⟨a, rfl⟩ := ProperCycleLinearity.cycleToChowQ_surjective (X.componentVariety D).presentation 1 a
  rw [ChowPushforwardMap.map_mk, Clopen.Chow.DivisorRestriction.map_mk,
    ← Clopen.CycleMaps.embed_eq_pushforward (Component.Image.inclusion X D) m,
    restrict_embed_other X m C D hCD, map_zero]

variable {X} {Y : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (P : ProperCycleLinearity.ProductPresentation X Y)
  (f : X.toOver ⟶ Y.toOver) (n : ℕ) [SmoothOfRelativeDimension n Y.structureMap]

theorem pull (C : irreducibleComponents X.carrier) (a : ProperCycleLinearity.ChowQ Y 1) :
    Clopen.Chow.DivisorRestriction.map (Component.Image.inclusion X C) m
      (General.DivisorPullback.pull P f m n a) =
      General.DivisorPullback.pull (ProductRestriction.presentation P (Component.Image.inclusion X C))
        (Component.Image.inclusion X C ≫ f) m n a := by
  let := Fintype.ofFinite (irreducibleComponents X.carrier)
  rw [PullbackComponentSum.sum P f m n, map_sum, Finset.sum_eq_single C]
  · exact Clopen.Chow.DivisorRestriction.map_push (Component.Image.inclusion X C) m _
  · intro D _ hD
    exact map_push_other X m C D (Ne.symm hD) _
  · simp

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Divisor.ComponentRestriction
