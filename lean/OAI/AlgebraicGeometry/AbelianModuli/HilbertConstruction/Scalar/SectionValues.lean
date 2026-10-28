import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

/-! # Section Values -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionValues

noncomputable section

/-! Multiplication of an actual module-sheaf section by an arbitrary global regular function. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def scalarSection {X : Scheme.{u}} {M : X.Modules} (r : Γ(X, ⊤))
    (s : Line.Bundles.structureModule X ⟶ M) : Line.Bundles.structureModule X ⟶ M :=
  (Global.Sections.structureModuleEndRingEquiv X).symm r ≫ s

theorem scalarSection_globalValue {X : Scheme.{u}} {M : X.Modules}
    (r : Γ(X, ⊤)) (s : Line.Bundles.structureModule X ⟶ M) :
    Global.Sections.moduleSectionHomEquiv M (scalarSection r s) = r • Global.Sections.moduleSectionHomEquiv M s := by
  have ha : ((Global.Sections.structureModuleEndRingEquiv X).symm r).app ⊤ (1 : Γ(X, ⊤)) = r :=
    (Global.Sections.structureModuleEndRingEquiv X).apply_symm_apply r
  change s.app ⊤ (((Global.Sections.structureModuleEndRingEquiv X).symm r).app ⊤ (1 : Γ(X, ⊤))) =
    r • s.app ⊤ (1 : Γ(X, ⊤))
  rw [ha]
  exact (congrArg (s.app ⊤) (mul_one r)).symm.trans (s.app_smul r (1 : Γ(X, ⊤)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.SectionValues
