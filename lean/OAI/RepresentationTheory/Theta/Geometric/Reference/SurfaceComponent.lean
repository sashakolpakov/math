import OAI.RepresentationTheory.Theta.Geometric.ComponentDimensionLower
import OAI.RepresentationTheory.Theta.Geometric.ComponentDimensionBound

/-! # Surface Component -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

/-! The original moduli problem has an actual integral projective
surface component containing a reference ball point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
    [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
    (D : Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem Data.ActiveHeckeThetaData.exists_reference_surface_component (hg : D.pel.HasIntegralModelGeometry)
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) :
    ∃ j : Fin D.pel.componentCount, (D.componentVariety hg j).complexDimension = 2 ∧
      ∃ a : D.domain, ∃ x : (D.componentVariety hg j).analyticSpace,
        x ≫ D.componentComplexInclusion j = D.referenceModuliMap hg a := by
  obtain ⟨j, hj, ha⟩ := D.exists_reference_component_dimension_at_least_two hg
  exact ⟨j, le_antisymm (D.component_dimension_le_two hg hs hdegree j) hj, ha⟩

end

end OAI.RepresentationTheory.Theta.Geometric
