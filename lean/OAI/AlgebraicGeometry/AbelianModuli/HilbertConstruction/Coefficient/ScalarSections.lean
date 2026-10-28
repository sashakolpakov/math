import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ZeroSections

/-! # Scalar Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ScalarSections

noncomputable section

/-! Scalar multiplication of actual sections agrees with the coefficient action on their global values and cannot enlarge their nonvanishing opens. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K))

def coefficientScalarSection {M : X.Modules} (c : K) (s : Line.Bundles.structureModule X ⟶ M) :
    Line.Bundles.structureModule X ⟶ M := (Global.Sections.structureModuleEndRingEquiv X).symm (ModulePresheaf.schemeCoefficientMap p c) ≫ s

theorem coefficientScalarSection_value {M : X.Modules} (c : K) (s : Line.Bundles.structureModule X ⟶ M) :
    (show (GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M from Global.Sections.moduleSectionHomEquiv M (coefficientScalarSection p c s)) =
      c • (show (GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M from Global.Sections.moduleSectionHomEquiv M s) := by
  have ha : ((Global.Sections.structureModuleEndRingEquiv X).symm (ModulePresheaf.schemeCoefficientMap p c)).app ⊤
      (1 : Γ(X, ⊤)) = ModulePresheaf.schemeCoefficientMap p c := (Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply _
  change s.app ⊤ (((Global.Sections.structureModuleEndRingEquiv X).symm (ModulePresheaf.schemeCoefficientMap p c)).app ⊤ (1 : Γ(X, ⊤))) =
    (X.presheaf.map (𝟙 (.op (⊤ : X.Opens))) (ModulePresheaf.schemeCoefficientMap p c)) • s.app ⊤ (1 : Γ(X, ⊤))
  rw [ha, X.presheaf.map_id]
  exact (congrArg (s.app ⊤) (mul_one (ModulePresheaf.schemeCoefficientMap p c))).symm.trans
    (s.app_smul (ModulePresheaf.schemeCoefficientMap p c) (1 : Γ(X, ⊤)))

theorem coefficientScalarSection_nonvanishing_le (L : Line.Bundles.LineBundle X) (c : K)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) :
    Ample.LineBundles.sectionNonvanishing (coefficientScalarSection p c s) ≤ Ample.LineBundles.sectionNonvanishing s := by
  by_cases hc : c = 0
  · subst c
    have he : coefficientScalarSection p 0 s = 0 := by
      simp only [coefficientScalarSection, map_zero, zero_comp]
    rw [he, L.sectionNonvanishing_zero]
    exact bot_le
  · have ha : IsUnit ((Global.Sections.structureModuleEndRingEquiv X).symm (ModulePresheaf.schemeCoefficientMap p c)) :=
      ((isUnit_iff_ne_zero.mpr hc).map (ModulePresheaf.schemeCoefficientMap p)).map (Global.Sections.structureModuleEndRingEquiv X).symm.toRingHom
    have : IsIso ((Global.Sections.structureModuleEndRingEquiv X).symm (ModulePresheaf.schemeCoefficientMap p c)) :=
      (isUnit_iff_isIso _).mp ha
    exact (Section.SectionRestriction.sectionNonvanishing_sourceIso (asIso ((Global.Sections.structureModuleEndRingEquiv X).symm (ModulePresheaf.schemeCoefficientMap p c))) s).le

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ScalarSections
