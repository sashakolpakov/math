import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalSectionPullbackValues
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BaseTopSectionEquiv
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Section.ResidueNonvanishing

/-! # Base Point Section Map -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasePointSectionMap

noncomputable section

/-! Actual evaluation at a residue-field scheme is semilinear over
the original base. Its kernel is exactly the sections not framing at
that point, so this vanishing condition is closed under linear combinations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

universe u

def basePointSectionMap {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (x : X) :
    (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤) →ₛₗ[(X.fromSpecResidueField x ≫ f).appTop.hom]
      Γ((Scheme.Modules.pullback (X.fromSpecResidueField x)).obj M, ⊤) := by
  letI := SheafCohomology.Projective.BaseZeroSections.baseGlobalSectionsModule f M
  let e := BaseTopSectionEquiv.baseTopSectionEquiv f M
  let a := X.fromSpecResidueField x
  let p := GlobalSectionPullbackValues.pullbackTopLinearMap a M
  refine { toFun := fun s => p (e.symm s), map_add' := ?_, map_smul' := ?_ }
  · intro s t
    rw [e.symm.map_add, p.map_add]
  · intro r s
    rw [e.symm.map_smul]
    change p (f.appTop r • e.symm s) = a.appTop (f.appTop r) • p (e.symm s)
    exact p.map_smulₛₗ (f.appTop r) (e.symm s)

theorem basePointSectionMap_value {X S : Scheme.{u}} (f : X ⟶ S) (M : X.Modules) (x : X)
    (s : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f M).obj (op ⊤)) :
    basePointSectionMap f M x s = CechPullbackSectionNormalization.pullbackTopSection (X.fromSpecResidueField x) M s :=
  congrArg (CechPullbackSectionNormalization.pullbackTopSection (X.fromSpecResidueField x) M)
    (BaseTopSectionEquiv.baseTopSectionEquiv_symm_apply f M s)

theorem basePointSectionMap_eq_zero_iff {X S : Scheme.{u}} (f : X ⟶ S)
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (x : X) (v : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf f L.sheaf).obj (op ⊤)) :
    basePointSectionMap f L.sheaf x v = 0 ↔
      x ∉ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm v) := by
  let s := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm v
  let a := X.fromSpecResidueField x
  let P := (Scheme.Modules.pullback a).obj L.sheaf
  have hv : basePointSectionMap f L.sheaf x v =
      AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P (AbelianModuli.HilbertConstruction.Ample.LineBundles.pullbackSection a s) := by
    rw [basePointSectionMap_value]
    exact (congrArg (CechPullbackSectionNormalization.pullbackTopSection a L.sheaf)
      ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).apply_symm_apply v).symm).trans
        (GlobalSectionPullbackValues.pullbackTopSection_hom_value a s)
  rw [hv, Section.ResidueNonvanishing.mem_sectionNonvanishing_iff_residue_pullback_ne_zero, not_ne_iff]
  constructor
  · intro h
    apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P).injective
    exact h
  · intro h
    rw [h]
    rfl

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasePointSectionMap
