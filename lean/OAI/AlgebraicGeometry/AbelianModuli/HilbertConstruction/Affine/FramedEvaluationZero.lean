import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedSectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionValueChange

/-! # Framed Evaluation Zero -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedEvaluationZero

noncomputable section

/-! Framed affine evaluation retains exact zero sections, and a frame
section evaluates to a unit. Both statements hold over arbitrary rings. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (L : Line.Bundles.LineBundle X) (x : Spec (.of R) ⟶ X)
variable (e : (L.pullback x).sheaf ≅ Line.Bundles.structureModule (Spec (.of R)))

theorem affineFramedSectionValue_eq_zero_iff (a : Line.Bundles.structureModule X ⟶ L.sheaf) :
    FramedSectionEvaluation.affineFramedSectionValue L x e a = 0 ↔ Ample.LineBundles.pullbackSection x a = 0 := by
  constructor
  · intro ha
    have hv : Frame.Coordinates.structureModuleEndValue (Spec (.of R)) (Ample.LineBundles.pullbackSection x a ≫ e.hom) = 0 := by
      apply (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.injective
      exact ha.trans (map_zero _).symm
    have hh : Ample.LineBundles.pullbackSection x a ≫ e.hom = 0 := by
      apply (Global.Sections.structureModuleEndRingEquiv (Spec (.of R))).injective
      exact hv.trans (map_zero _).symm
    apply (cancel_mono e.hom).mp
    simpa only [zero_comp] using hh
  · intro ha
    simp only [FramedSectionEvaluation.affineFramedSectionValue, Family.FramedSectionEvaluation.familyFramedSectionValue, ha, zero_comp, map_zero]

theorem affineFramedSectionValue_isUnit_of_frame (a : Line.Bundles.structureModule X ⟶ L.sheaf)
    [IsIso (Ample.LineBundles.pullbackSection x a)] : IsUnit (FramedSectionEvaluation.affineFramedSectionValue L x e a) := by
  have hu : IsUnit (Frame.Coordinates.structureModuleEndValue (Spec (.of R)) (Ample.LineBundles.pullbackSection x a ≫ e.hom)) :=
    (Global.Sections.structureModuleEnd_isIso_iff (Ample.LineBundles.pullbackSection x a ≫ e.hom)).mp inferInstance
  exact hu.map (Scheme.ΓSpecIso (.of R)).hom.hom

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.FramedEvaluationZero
