import OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenSectionLifts
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Scalar.SectionNonvanishing

/-! # Basic Open Section Nonvanishing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenSectionNonvanishing

noncomputable section

/-! Clearing a denominator and multiplying once more by the principal
function extends a local section with exactly its original nonvanishing open. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem exists_global_section_nonvanishing_eq_basicOpen_image
    {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (r : Γ(X, ⊤))
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (X.basicOpen r).toScheme ⟶ (BasicOpenSectionLifts.restrictedLineBundle L (X.basicOpen r)).sheaf) :
    ∃ q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf,
      AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q = (X.basicOpen r).ι ''ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := by
  let U := X.basicOpen r
  let P := BasicOpenSectionLifts.restrictedLineBundle L U
  obtain ⟨n, q₀, hq₀⟩ := BasicOpenSectionLifts.exists_global_restriction_power L r t
  have hunit : IsUnit (U.ι.appTop r) := by
    apply (AbelianModuli.HilbertConstruction.Scalar.Nonvanishing.global_isUnit_iff_basicOpen_eq_top _).mpr
    rw [← U.ι.preimage_basicOpen_top]
    change U.ι ⁻¹ᵁ U = ⊤
    ext y
    exact iff_true_intro y.property
  have he : AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q₀ = (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P.sheaf).symm
      ((U.ι.appTop r) ^ n • AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P.sheaf t) := by
    apply (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P.sheaf).injective
    exact hq₀.trans ((AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P.sheaf).apply_symm_apply _).symm
  have hlocal : AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q₀) = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := by
    rw [he, Scalar.SectionNonvanishing.sectionNonvanishing_smul_value P, U.toScheme.basicOpen_of_isUnit (hunit.pow n),
      top_inf_eq, (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv P.sheaf).symm_apply_apply]
  have hpre : U.ι ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q₀ = AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t :=
    (AbelianModuli.HilbertConstruction.Section.SectionRestriction.sectionNonvanishing_restrictSection U.ι q₀).symm.trans hlocal
  let q := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm
    (r • AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf q₀)
  refine ⟨q, ?_⟩
  calc
    AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q = U ⊓ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q₀ := by
      dsimp only [q]
      rw [Scalar.SectionNonvanishing.sectionNonvanishing_smul_value, (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm_apply_apply]
    _ = U.ι ''ᵁ (U.ι ⁻¹ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing q₀) := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    _ = U.ι ''ᵁ AbelianModuli.HilbertConstruction.Ample.LineBundles.sectionNonvanishing t := congrArg (U.ι ''ᵁ ·) hpre

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenSectionNonvanishing
