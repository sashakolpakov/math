import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.SupportedCycle
import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.IntersectionZero

/-! # Component -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Component

noncomputable section

/-! Proper intersections supported in an actual component commute with
restriction and embedding, in arbitrary codimensions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped Classical

open OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.ProperCycleLinearity OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.Image OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Component.CycleMaps OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.CycleSupport
  Supports.ProperCycle

theorem supported_right (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p q : ℕ)
    (a : X.RationalDimensionCycle p) (b : X.RationalDimensionCycle q)
    (c : X.RationalDimensionCycle (p + q)) (hc : CycleClass.Thom.IntersectionGeometry.IsProperIntersectionCycle X p q a b c)
    (S : Closeds X.carrier) (hb : CycleSupport.SupportedOn X q b S) : CycleSupport.SupportedOn X (p + q) c S := by
  intro C hC
  apply (Supports.supportPoint_mem_iff_subset S C.val).mp
  by_contra hn
  have hz : c C = 0 := by
    rw [hc.2 C]
    apply Finset.sum_eq_zero
    intro A _
    apply Finset.sum_eq_zero
    intro B hB
    have hi : CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val = 0 :=
      dite_eq_right (fun h => hn (hb B hB h.2))
    change a A * b B * CycleClass.Thom.IntersectionGeometry.intersectionMultiplicity X A.val B.val C.val = 0
    rw [hi, mul_zero]
  exact (Finsupp.mem_support_iff.mp hC) hz

theorem intersection_embed (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p q : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (C : irreducibleComponents X.carrier)
    (a : X.RationalDimensionCycle p)
    (A : (X.componentVariety C).presentation.DimensionCycleSupport q)
    (hp : CycleClass.Thom.IntersectionGeometry.MeetProperly X p q a (Finsupp.single (Component.Image.supportImage X C q A) 1)) :
    letI := Component.Image.component_relativeDimension X m C
    Supports.ProperCycle.intersectionBilinear X m p q a (Finsupp.single (Component.Image.supportImage X C q A) 1) =
      Component.CycleMaps.embed X C (p + q) (Supports.ProperCycle.intersectionBilinear (X.componentVariety C).presentation m p q
        (Component.CycleMaps.restrict X C p a) (Finsupp.single A 1)) := by
  let := Component.Image.component_relativeDimension X m C
  rw [← Component.Bilinear.restrict_single_image X C q A 1,
    ← Component.Bilinear.restrict_bilinear]
  symm
  apply Component.SupportedCycle.embed_restrict
  have hs := supported_right X p q _ _ _ (Supports.ProperCycle.intersectionBilinear_isProper X m p q _ _ hp)
    ⟨(Component.Image.supportImage X C q A).val, (Component.Image.supportImage X C q A).val.isClosed⟩ (by
      intro B hB
      have he : B = Component.Image.supportImage X C q A := by simpa using hB
      subst B
      exact Set.Subset.rfl)
  intro B hB
  exact (hs B hB).trans (X.componentSupportImage_subset C A.val)

theorem singleton (X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (m p : ℕ)
    [SmoothOfRelativeDimension m X.structureMap] (B : X.DimensionCycleSupport p)
    (a : X.RationalDimensionCycle p)
    (ha : CycleSupport.SupportedOn X p a ⟨B.val, B.val.isClosed⟩) : a = Finsupp.single B (a B) := by
  ext C
  by_cases he : B = C
  · subst C
    rw [Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne' he]
    by_contra hn
    have hCB : C.val ≤ B.val := ha C (Finsupp.mem_support_iff.mpr hn)
    exact he (Subtype.ext (IntersectionZero.eq_of_subset_of_codimension_eq X m hCB
      (C.property.trans B.property.symm)).symm)

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.General.Component
