import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoCoefficientSectionBasis
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionBundleTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsPushforward

/-! # Iso Scheme Section Equiv -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoSchemeSectionEquiv

noncomputable section

/-! Scheme isomorphisms over Spec R induce R-linear equivalences of
actual sections, with the map explicitly given by section pullback.
Composing with a sheaf isomorphism retains that concrete formula. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {X Y : Over (Spec (.of R))}
variable (e : X ≅ Y) (M : Y.left.Modules)

local instance sourceSchemeHom_isIso : IsIso e.hom.left :=
  inferInstanceAs (IsIso ((Over.forget (Spec (.of R))).map e.hom))

def sourceIsoSchemeSectionMap :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor Y.hom).obj M →ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj ((Scheme.Modules.pullback e.hom.left).obj M) where
  toFun v := Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) _
    (Ample.LineBundles.pullbackSection e.hom.left ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).symm v))
  map_add' v w := by
    rw [map_add, Section.NonvanishingAddition.pullbackSection_add, map_add]
  map_smul' r v := by
    have hs : (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).symm (r • v) =
        Scalar.SectionValues.scalarSection (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom r)
          ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).symm v) := by
      apply (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).injective
      rw [AddEquiv.apply_symm_apply, Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar, AddEquiv.apply_symm_apply]
    have hw : e.hom.left.appTop (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom r) = Coefficient.ModulePresheaf.schemeCoefficientMap X.hom r :=
      (RingHom.congr_fun (Coefficient.GlobalSectionsPushforward.schemeCoefficientMap_comp e.hom.left Y.hom) r).symm.trans
        (congrArg (fun f : X.left ⟶ Spec (.of R) => Coefficient.ModulePresheaf.schemeCoefficientMap f r) e.hom.w)
    change Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) _
      (Ample.LineBundles.pullbackSection e.hom.left
        ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).symm (r • v))) = _
    rw [hs, Coefficient.RingSectionBasis.pullbackSection_scalarSection, hw]
    exact Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv_scalar (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) _ r _

def sourceIsoSchemeSectionEquiv :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor Y.hom).obj M ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj ((Scheme.Modules.pullback e.hom.left).obj M) :=
  LinearEquiv.ofBijective (sourceIsoSchemeSectionMap e M)
    ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) _).bijective.comp
      ((IsoCoefficientSectionBasis.pullbackSection_bijective_of_isIso e.hom.left M).comp
        (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).symm.bijective))

def sourceBundleIsoSchemeSectionEquiv {L : X.left.Modules}
    (H : (Scheme.Modules.pullback e.hom.left).obj M ≅ L) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor Y.hom).obj M ≃ₗ[R] (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor X.hom).obj L :=
  (sourceIsoSchemeSectionEquiv e M).trans (Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) H)

theorem sourceBundleIsoSchemeSectionEquiv_section {L : X.left.Modules}
    (H : (Scheme.Modules.pullback e.hom.left).obj M ≅ L) (s : Line.Bundles.structureModule Y.left ⟶ M) :
    sourceBundleIsoSchemeSectionEquiv e M H
      (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M s) =
      Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) L (Ample.LineBundles.pullbackSection e.hom.left s ≫ H.hom) := by
  change Coefficient.SectionBundleTransport.coefficientBundleSectionEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) H
    (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) _
      (Ample.LineBundles.pullbackSection e.hom.left
        ((Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M).symm
          (Coefficient.RingSectionBasis.coefficientRingSectionAddEquiv (Coefficient.ModulePresheaf.schemeCoefficientMap Y.hom) M s)))) = _
  rw [AddEquiv.symm_apply_apply]
  exact (Coefficient.SectionBundleTransport.coefficientRingSectionAddEquiv_postcomp (Coefficient.ModulePresheaf.schemeCoefficientMap X.hom) H.hom _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IsoSchemeSectionEquiv
