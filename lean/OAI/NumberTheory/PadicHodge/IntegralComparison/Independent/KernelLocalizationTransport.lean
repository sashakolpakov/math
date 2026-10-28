import OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.LocalizedKernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Kernel Localization Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.KernelLocalizationTransport

noncomputable section

open _root_.CategoryTheory Limits

universe u v w

variable {R : Type u} [CommRing R] {C : Type v} [Category.{w} C] [HasZeroMorphisms C]
  {M N : C} (f : M ⟶ N) [HasKernel f]
  (F G : C ⥤ ModuleCat.{u} R) [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
  [PreservesLimit (parallelPair f 0) F] [PreservesLimit (parallelPair f 0) G]
  (τ : F ⟶ G)

def kernelIso (H : C ⥤ ModuleCat.{u} R) [H.PreservesZeroMorphisms]
    [PreservesLimit (parallelPair f 0) H] :
    H.obj (kernel f) ≅ ModuleCat.of R (H.map f).hom.ker :=
  PreservesKernel.iso H f ≪≫ ModuleCat.kernelIsoKer (H.map f)

@[simp]
theorem kernelIso_subtype (H : C ⥤ ModuleCat.{u} R)
    [H.PreservesZeroMorphisms] [PreservesLimit (parallelPair f 0) H] :
    (kernelIso f H).hom ≫ ModuleCat.ofHom (H.map f).hom.ker.subtype =
      H.map (kernel.ι f) := by
  simp [kernelIso, PreservesKernel.iso_hom, kernelComparison_comp_ι]

theorem isLocalized (S : Submonoid R)
    [IsLocalizedModule S (τ.app M).hom] [IsLocalizedModule S (τ.app N).hom] :
    IsLocalizedModule S (τ.app (kernel f)).hom := by
  have h : ∀ x, (G.map f).hom ((τ.app M).hom x) =
      (τ.app N).hom ((F.map f).hom x) := by
    intro x
    exact congrArg (fun k => k.hom x) (τ.naturality f).symm
  let φ := LocalizedKernels.map (F.map f).hom (G.map f).hom
    (τ.app M).hom (τ.app N).hom h
  have hφ : IsLocalizedModule S φ :=
    LocalizedKernels.isLocalized _ _ _ _ h S
  have heq : (kernelIso f F).hom ≫ ModuleCat.ofHom φ =
      τ.app (kernel f) ≫ (kernelIso f G).hom := by
    apply (cancel_mono (ModuleCat.ofHom (G.map f).hom.ker.subtype)).mp
    have hsub : ModuleCat.ofHom φ ≫ ModuleCat.ofHom (G.map f).hom.ker.subtype =
        ModuleCat.ofHom (F.map f).hom.ker.subtype ≫ τ.app M := rfl
    rw [Category.assoc, hsub, ← Category.assoc, kernelIso_subtype,
      Category.assoc, kernelIso_subtype]
    exact τ.naturality (kernel.ι f)
  apply (IsLocalizedModule.comp_iff_of_bijective_left S (kernelIso f G).hom.hom
    (ConcreteCategory.bijective_of_isIso _)).mp
  rw [← ModuleCat.hom_comp, ← heq, ModuleCat.hom_comp]
  exact (IsLocalizedModule.comp_iff_of_bijective_right S (kernelIso f F).hom.hom
    (ConcreteCategory.bijective_of_isIso _)).mpr hφ

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Independent.KernelLocalizationTransport
