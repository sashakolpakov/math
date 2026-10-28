import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Family.FramedSectionEvaluation

/-! # Section Value Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionValueChange

noncomputable section

/-! Changing a frame multiplies every section value by the same actual
unit of the base ring. No choice of section enters the multiplier. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {M : S.Modules}

theorem framedSectionValue_change (e f : M ≅ Line.Bundles.structureModule S)
    (a : Line.Bundles.structureModule S ⟶ M) :
    Frame.Coordinates.structureModuleEndValue S (a ≫ f.hom) =
      Frame.Coordinates.structureModuleEndValue S (e.inv ≫ f.hom) * Frame.Coordinates.structureModuleEndValue S (a ≫ e.hom) := by
  have he : a ≫ f.hom = (a ≫ e.hom) ≫ (e.inv ≫ f.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [he]
  exact (Frame.Coordinates.structureModuleEndValue S).map_mul (e.inv ≫ f.hom) (a ≫ e.hom)

theorem framedSectionValue_change_unit (e f : M ≅ Line.Bundles.structureModule S) :
    IsUnit (Frame.Coordinates.structureModuleEndValue S (e.inv ≫ f.hom)) :=
  (Global.Sections.structureModuleEnd_isIso_iff _).mp inferInstance

theorem familyFramedSectionValue_change {X : Scheme.{u}} (L : Line.Bundles.LineBundle X) (x : S ⟶ X)
    (e f : (L.pullback x).sheaf ≅ Line.Bundles.structureModule S) :
    ∃ u : Γ(S, ⊤)ˣ, ∀ a : Line.Bundles.structureModule X ⟶ L.sheaf,
      Family.FramedSectionEvaluation.familyFramedSectionValue L x f a = (u : Γ(S, ⊤)) * Family.FramedSectionEvaluation.familyFramedSectionValue L x e a := by
  let h := framedSectionValue_change_unit e f
  refine ⟨h.unit, fun a => ?_⟩
  rw [h.unit_spec]
  exact framedSectionValue_change e f (Ample.LineBundles.pullbackSection x a)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Framed.SectionValueChange
