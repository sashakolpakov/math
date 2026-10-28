import OAI.AlgebraicGeometry.PELModuli.IntegralModel.GlobalBasicOpenLocalization
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictionTopValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! # Basic Open Section Lifts -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenSectionLifts

noncomputable section

/-! Actual sections on a principal open extend after multiplication
by a power of its defining global regular function. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite
open _root_.AlgebraicGeometry.Scheme.Modules

open OAI.AlgebraicGeometry.PELModuli.IntegralModel.RestrictionTopValues.PolarizationEmbedding
universe u

def restrictedLineBundle {X : Scheme.{u}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (U : X.Opens) : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle U.toScheme where
  sheaf := L.sheaf.restrict U.ι
  locallyTrivial x := by
    obtain ⟨V, hx, ⟨e⟩⟩ := (L.pullback U.ι).locallyTrivial x
    exact ⟨V, hx, ⟨(Scheme.Modules.pullback V.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.sheaf) ≪≫ e⟩⟩

theorem restrictionTopIso_section_value
    {X : Scheme.{u}} {M : X.Modules} (U : X.Opens) (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M) :
    (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso M U).hom (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv (M.restrict U.ι) (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection U.ι q)) =
      M.presheaf.map U.leTop.op (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv M q) := by
  rw [AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv_apply, RestrictionTopValues.PolarizationEmbedding.restrictSection_top_value]
  rw [U.topIso.hom.hom.map_one]
  have h := PresheafOfModules.naturality_apply q.val U.leTop.op (1 : Γ(X, ⊤))
  change q.app U (X.presheaf.map U.leTop.op (1 : Γ(X, ⊤))) =
    M.presheaf.map U.leTop.op (q.app ⊤ (1 : Γ(X, ⊤))) at h
  rw [(X.presheaf.map U.leTop.op).hom.map_one] at h
  exact h

theorem topIso_ι_appTop
    {X : Scheme.{u}} (U : X.Opens) (r : Γ(X, ⊤)) :
    U.topIso.hom (U.ι.appTop r) = X.presheaf.map U.leTop.op r := by
  rw [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appTop]
  exact (ConcreteCategory.congr_hom (X.presheaf.map_comp
    (homOfLE (show U.ι ''ᵁ (⊤ : U.toScheme.Opens) ≤ ⊤ from le_top)).op
    (eqToHom U.ι_image_top.symm).op) r).symm

theorem exists_global_restriction_power
    {X : Scheme.{u}} [X.IsSeparated] [CompactSpace X]
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (r : Γ(X, ⊤))
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule (X.basicOpen r).toScheme ⟶ (restrictedLineBundle L (X.basicOpen r)).sheaf) :
    ∃ (n : ℕ) (q : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ L.sheaf),
      AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv (L.sheaf.restrict (X.basicOpen r).ι) (AbelianModuli.HilbertConstruction.Section.SectionRestriction.restrictSection (X.basicOpen r).ι q) =
        ((X.basicOpen r).ι.appTop r) ^ n •
          AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv (L.sheaf.restrict (X.basicOpen r).ι) t := by
  let U := X.basicOpen r
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have := GlobalBasicOpenLocalization.globalBasicOpen_isLocalized L.sheaf r
  let v := AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv (L.sheaf.restrict U.ι) t
  let z : (SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) L.sheaf).obj (op U) := (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso L.sheaf U).hom v
  obtain ⟨⟨w, c⟩, hw⟩ := IsLocalizedModule.surj (Submonoid.powers r)
    ((SheafCohomology.Cech.SchemeModuleBaseBasic.Scheme.Modules.baseModulePresheaf (𝟙 X) L.sheaf).map U.leTop.op).hom z
  obtain ⟨n, hn⟩ := c.property
  let q := (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).symm w
  refine ⟨n, q, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso (SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso L.sheaf U).hom).injective
  rw [restrictionTopIso_section_value, (AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv L.sheaf).apply_symm_apply,
    SheafCohomology.Projective.CanonicalAffineFrame.restrictionTopIso_smul, U.topIso.hom.hom.map_pow, topIso_ι_appTop,
    ← (X.presheaf.map U.leTop.op).hom.map_pow]
  let z' : Γ(L.sheaf, U) := z
  change X.presheaf.map U.leTop.op (c : Γ(X, ⊤)) • z' =
    L.sheaf.presheaf.map U.leTop.op w at hw
  rw [← hn] at hw
  exact hw.symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.BasicOpenSectionLifts
