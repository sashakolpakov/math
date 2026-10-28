import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Bilinear
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Symmetry

/-! # Supported Cycle -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.SupportedCycle

noncomputable section

/-! A cycle supported in one actual component is recovered by restriction
and embedding. This applies to proper divisor intersections with a cycle
supported in that component. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport
  Supports.ProperCycle

theorem embed_restrict (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (C : irreducibleComponents X.carrier)
    (p : ℕ) (a : X.RationalDimensionCycle p)
    (ha : ∀ A ∈ a.support, (A.val : Set X.carrier) ⊆ C.val) :
    CycleMaps.embed X C p (CycleMaps.restrict X C p a) = a := by
  ext A
  rw [Principal.CycleDecomposition.embed_restrict_apply]
  split_ifs with h
  · rfl
  · symm
    by_contra hn
    exact h (X.supportComponent_eq_of_subset A.val C (ha A (Finsupp.mem_support_iff.mpr hn)))

theorem intersection_embed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : irreducibleComponents X.carrier)
    (a : X.RationalDimensionCycle 1)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport 1)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X 1 1 a (Finsupp.single (Image.supportImage X C 1 A) 1)) :
    letI := Image.component_relativeDimension X m C
    Supports.ProperCycle.intersectionBilinear X m 1 1 a (Finsupp.single (Image.supportImage X C 1 A) 1) =
      CycleMaps.embed X C 2 (Supports.ProperCycle.intersectionBilinear (X.componentVariety C).presentation m 1 1
        (CycleMaps.restrict X C 1 a) (Finsupp.single A 1)) := by
  let := Image.component_relativeDimension X m C
  rw [← Bilinear.restrict_single_image X C 1 A 1,
    ← Bilinear.restrict_bilinear]
  symm
  apply embed_restrict
  have hc := Symmetry.proper_cycle_comm X m _ _ _
    (Supports.ProperCycle.intersectionBilinear_isProper X m 1 1 _ _ hp)
  have hs := CycleSupport.proper_intersection X 1 1 _ _ _ hc
    ⟨(Image.supportImage X C 1 A).val, (Image.supportImage X C 1 A).val.isClosed⟩ (by
      intro B hB
      have he : B = Image.supportImage X C 1 A := by simpa using hB
      subst B
      exact Set.Subset.rfl)
  intro B hB
  exact (hs B hB).trans (X.componentSupportImage_subset C A.val)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.SupportedCycle
