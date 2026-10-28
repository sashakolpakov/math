import OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenPrincipalIdealRestriction
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.IdealOpenGenerator
import OAI.AlgebraicGeometry.Divisors.LineBundles.Scheme.ModuleBasisIso

/-! # Open Principal Ideal Module -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenPrincipalIdealModule.BundleCycles

noncomputable section

/-! A regular principal image ideal on an affine open supplies a
genuine local frame of the ambient scheme's ideal module. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Z : Scheme.{0}} (f : Z ⟶ X) [QuasiCompact f]
    (U : X.affineOpens) (t : Γ(X, U.1))
    (hker : RingHom.ker (f.app U.1).hom = Ideal.span {t})

def affineOpenPrincipalIdealSection : Γ(LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule f, U.1) :=
  (LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso f U.1).inv ⟨t, hker.symm ▸ Ideal.subset_span (Set.mem_singleton t)⟩

omit [QuasiCompact f] in
theorem affineOpenPrincipalIdealSection_image :
    (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModuleInclusion f).app U.1 (affineOpenPrincipalIdealSection f U t hker) = t :=
  LineBundles.Scheme.IdealModule.BundleCycles.schemeIdealModuleSectionsIso_inv_apply f U.1 _

theorem affineOpenPrincipalIdealSectionHom_isIso (ht : IsRegular t) :
    IsIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule f) U.1 (affineOpenPrincipalIdealSection f U t hker)) := by
  let : IsAffine U.1.toScheme := U.2
  apply LineBundles.Scheme.ModuleBasisIso.BundleCycles.schemeModule_isIso_of_basis _ (isBasis_basicOpen U.1.toScheme)
  rintro V ⟨r, rfl⟩
  have hi : U.1.ι ''ᵁ U.1.toScheme.basicOpen r = X.basicOpen (U.1.topIso.hom r) := by
    have he : U.1.topIso.inv (U.1.topIso.hom r) = r :=
      ConcreteCategory.congr_hom U.1.topIso.hom_inv_id r
    exact (congrArg (fun a => U.1.ι ''ᵁ U.1.toScheme.basicOpen a) he).symm.trans
      (U.1.ι_image_basicOpen_topIso_inv (U.1.topIso.hom r))
  apply LineBundles.Scheme.IdealOpenGenerator.BundleCycles.schemeIdealOpenSectionHom_bijective
  · rw [affineOpenPrincipalIdealSection_image]
    have H : ∀ (W : X.Opens) (hWU : W ≤ U.1), W = X.basicOpen (U.1.topIso.hom r) →
        IsRegular (X.presheaf.map (homOfLE hWU).op t) := by
      intro W hWU hW
      subst W
      exact OpenPrincipalIdealRestriction.BundleCycles.affineOpenPrincipal_regular_restriction U t ht (U.1.topIso.hom r)
    exact H _ _ hi
  · rw [affineOpenPrincipalIdealSection_image]
    have H : ∀ (W : X.Opens) (hWU : W ≤ U.1), W = X.basicOpen (U.1.topIso.hom r) →
        RingHom.ker (f.app W).hom = Ideal.span {X.presheaf.map (homOfLE hWU).op t} := by
      intro W hWU hW
      subst W
      exact OpenPrincipalIdealRestriction.BundleCycles.affineOpenPrincipal_kernel_restriction f U t hker (U.1.topIso.hom r)
    exact H _ _ hi

def affineOpenPrincipalIdealModuleIso (ht : IsRegular t) :
    (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule f).restrict U.1.ι ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule U.1.toScheme := by
  let := affineOpenPrincipalIdealSectionHom_isIso f U t hker ht
  exact (asIso (Module.SectionHom.BundleCycles.moduleSectionHomOnOpen (LineBundles.Scheme.SchemeIdealModule.BundleCycles.schemeIdealModule f) U.1 (affineOpenPrincipalIdealSection f U t hker))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Affine.OpenPrincipalIdealModule.BundleCycles
