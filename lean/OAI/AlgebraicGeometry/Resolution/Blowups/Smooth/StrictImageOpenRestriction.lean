import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.StrictImageCriterion
import OAI.AlgebraicGeometry.Resolution.Blowups.ClosedOpenIntermediate

/-! # Strict Image Open Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.StrictImageOpenRestriction.Construction

noncomputable section

/-! Agreement with a smooth closed center on the protected open makes the actual strict image smooth. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem schemeImage_smooth_of_closed_open_restriction
    {Z W Y : Scheme} [NoetherianSpace Z] [IsReduced Z]
    (i : Z ⟶ W) [IsClosedImmersion i] (j : W ⟶ Y) [IsOpenImmersion j]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (C : Y.IdealSheafData) [Smooth (C.subschemeι ≫ f)]
    (hC : C.comap j = i.ker) : Smooth ((i ≫ j).imageι ≫ f) := by
  have hle : C ≤ (i ≫ j).ker := by
    rw [← Scheme.IdealSheafData.map_ker]
    exact Scheme.IdealSheafData.le_map_iff_comap_le.mpr hC.le
  let a := ClosedOpenIntermediate.Construction.closedOpenIntermediateMap i j C hle
  let : IsOpenImmersion a := ClosedOpenIntermediate.Construction.closedOpenIntermediateMap_isOpenImmersion i j C hle hC
  have he : a ≫ C.subschemeι = i ≫ j := ClosedOpenIntermediate.Construction.closedOpenIntermediateMap_over i j C hle
  have h := StrictImageCriterion.Construction.schemeImage_smooth_of_open_closed_factorization a C.subschemeι f
  rwa [he] at h

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.StrictImageOpenRestriction.Construction
