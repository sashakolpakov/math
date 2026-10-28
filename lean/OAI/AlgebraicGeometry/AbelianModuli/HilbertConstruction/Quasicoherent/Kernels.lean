import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.QuasicoherentKernels
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.IsoImage
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.QuasicoherenceLocality

/-! # Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels

noncomputable section

/-! Kernels of morphisms of quasicoherent scheme modules are quasicoherent. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

theorem affine_quasicoherent_kernel {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let F := pushforward X.toSpecΓ
  have : (F.obj M).IsQuasicoherent := IsoImage.modulePushforward_quasicoherent_of_isIso X.toSpecΓ M
  have : (F.obj N).IsQuasicoherent := IsoImage.modulePushforward_quasicoherent_of_isIso X.toSpecΓ N
  have hk : (kernel (F.map f)).IsQuasicoherent := HilbertConstruction.Spec.QuasicoherentKernels.spec_quasicoherent_kernel (F.map f)
  have : (F.obj (kernel f)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, ⊤)).ringCatSheaf).prop_of_iso
      (PreservesKernel.iso F f).symm hk
  have hr : ((F.obj (kernel f)).restrict X.toSpecΓ).IsQuasicoherent := inferInstance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((restrictFunctorAdjCounitIso X.toSpecΓ).app (kernel f)) hr

theorem module_quasicoherent_kernel {X : Scheme.{u}}
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  apply Module.QuasicoherenceLocality.module_quasicoherent_of_affine_restrictions
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := restrictFunctor U.1.ι
  have : PreservesLimits F := Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits U.1.ι
  have hk : (kernel (F.map f)).IsQuasicoherent := affine_quasicoherent_kernel (F.map f)
  exact (SheafOfModules.isQuasicoherent U.1.toScheme.ringCatSheaf).prop_of_iso
    (PreservesKernel.iso F f).symm hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Kernels
