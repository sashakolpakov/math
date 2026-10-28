import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasePointSectionMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing

/-! # Section Nonvanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionNonvanishing

noncomputable section

/-! Multiplication of an actual global line-bundle section by a regular
function intersects its nonvanishing open with the function's basic open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Scalar.Nonvanishing
universe u

theorem pullbackTopSection_ne_zero_iff_nonvanishing
    {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (v : Γ(L.sheaf, ⊤)) (x : X) :
    CechPullbackSectionNormalization.pullbackTopSection (X.fromSpecResidueField x) L.sheaf v ≠ 0 ↔
      x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm v) := by
  have h := not_congr (BasePointSectionMap.basePointSectionMap_eq_zero_iff (𝟙 X) L x v)
  simpa only [BasePointSectionMap.basePointSectionMap_value, not_not] using h

theorem residue_appTop_isUnit_iff_basicOpen
    {X : Scheme.{u}} (r : Γ(X, ⊤)) (x : X) :
    IsUnit ((X.fromSpecResidueField x).appTop r) ↔ x ∈ X.basicOpen r := by
  let a := X.fromSpecResidueField x
  rw [AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.global_isUnit_iff_basicOpen_eq_top, ← a.preimage_basicOpen_top]
  constructor
  · intro h
    have hy : (default : Spec (X.residueField x)) ∈ a ⁻¹ᵁ X.basicOpen r := h.symm ▸ trivial
    change a default ∈ X.basicOpen r at hy
    simpa only [a, Scheme.fromSpecResidueField_apply] using hy
  · intro h
    apply top_unique
    intro y _
    change a y ∈ X.basicOpen r
    simpa only [a, Scheme.fromSpecResidueField_apply] using h

theorem sectionNonvanishing_smul_value
    {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (r : Γ(X, ⊤)) (v : Γ(L.sheaf, ⊤)) :
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (r • v)) =
      X.basicOpen r ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm v) := by
  ext x
  change x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm (r • v)) ↔
    x ∈ X.basicOpen r ∧ x ∈ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm v)
  let a := X.fromSpecResidueField x
  have hfield : IsField Γ(Spec (X.residueField x), ⊤) :=
    (Scheme.ΓSpecIso (X.residueField x)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField (X.residueField x))
  let := hfield.toField
  rw [← pullbackTopSection_ne_zero_iff_nonvanishing,
    ← pullbackTopSection_ne_zero_iff_nonvanishing L v x,
    ← residue_appTop_isUnit_iff_basicOpen r x, isUnit_iff_ne_zero]
  have h := (GlobalSectionPullbackValues.pullbackTopLinearMap a L.sheaf).map_smulₛₗ r v
  change CechPullbackSectionNormalization.pullbackTopSection a L.sheaf (r • v) =
    a.appTop r • CechPullbackSectionNormalization.pullbackTopSection a L.sheaf v at h
  rw [h, smul_ne_zero_iff]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionNonvanishing
