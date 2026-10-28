import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ScalarSections

/-! # Scalar Section Global Value -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarSectionGlobalValue

noncomputable section

/-! Coefficient scalar sections have their expected value in the actual global module. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem coefficientScalarSection_globalValue
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    {M : X.Modules} (c : K) (s : Line.Bundles.structureModule X ⟶ M) :
    Global.Sections.moduleSectionHomEquiv M (Coefficient.ScalarSections.coefficientScalarSection p c s) =
      Coefficient.ModulePresheaf.schemeCoefficientMap p c • Global.Sections.moduleSectionHomEquiv M s := by
  have h := Coefficient.ScalarSections.coefficientScalarSection_value p c s
  change Global.Sections.moduleSectionHomEquiv M (Coefficient.ScalarSections.coefficientScalarSection p c s) =
    (X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) (Coefficient.ModulePresheaf.schemeCoefficientMap p c)) • Global.Sections.moduleSectionHomEquiv M s at h
  simpa only [X.presheaf.map_id, CommRingCat.id_apply] using h

theorem schemeCoefficientMap_globalValue
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))
    (c : Γ(Spec (.of K), ⊤)) :
    Coefficient.ModulePresheaf.schemeCoefficientMap p ((Scheme.ΓSpecIso (.of K)).hom c) = p.appTop c := by
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso (.of K)).hom_inv_id c
  exact congrArg p.appTop h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Field.ScalarSectionGlobalValue
