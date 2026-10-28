import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ZariskiExactness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality

/-! # Cokernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels

noncomputable section

/-! Cokernels of morphisms of actual quasicoherent module sheaves are quasicoherent. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
universe u

theorem affine_quasicoherent_cokernel {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent := by
  let F := restrictFunctor X.isoSpec.inv
  have hC : (cokernel (F.map f)).IsQuasicoherent :=
    Affine.ZariskiExactness.ZariskiCohomology.moduleSpec_isQuasicoherent_cokernel (F.map f)
  have : (F.obj (cokernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso F f).symm hC
  have hback : ((F.obj (cokernel f)).restrict X.isoSpec.hom).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((LineBundle.IsoImage.restrictFunctorInverseIso X.isoSpec).app (cokernel f)) hback

theorem module_quasicoherent_cokernel {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (cokernel f).IsQuasicoherent := by
  apply Module.QuasicoherenceLocality.module_quasicoherent_of_affine_restrictions
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := restrictFunctor U.1.ι
  have hC : (cokernel (F.map f)).IsQuasicoherent := affine_quasicoherent_cokernel (F.map f)
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso F f).symm hC

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Cokernels
