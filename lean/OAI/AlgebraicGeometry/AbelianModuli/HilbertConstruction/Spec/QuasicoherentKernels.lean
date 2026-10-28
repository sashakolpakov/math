/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.KernelSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Localized.ModuleSquares
import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-! # Quasicoherent Kernels -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.QuasicoherentKernels

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {R : CommRingCat.{u}}

theorem spec_quasicoherent_kernel
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) : (kernel f).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ]
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  intro r
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let m := ((modulesSpecToSheaf.obj M).obj.map U.leTop.op).hom
  let n := ((modulesSpecToSheaf.obj N).obj.map U.leTop.op).hom
  have hm : IsLocalizedModule.Away r m :=
    ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) r
  have hn : IsLocalizedModule.Away r n :=
    ((isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance) r
  let : IsLocalizedModule.Away r m := hm
  let : IsLocalizedModule.Away r n := hn
  let g := ((modulesSpecToSheaf.map f).hom.app (op ⊤)).hom
  let gU := ((modulesSpecToSheaf.map f).hom.app (op U)).hom
  have hmap : IsLocalizedModule.map (Submonoid.powers r) m n g = gU := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r) m n
    rw [IsLocalizedModule.map_comp]
    ext x
    change N.presheaf.map U.leTop.op (f.val.app (op ⊤) x) =
      f.val.app (op U) (M.presheaf.map U.leTop.op x)
    exact (ConcreteCategory.congr_hom (f.val.naturality U.leTop.op) x).symm
  let k := LinearMap.toKerIsLocalized (Submonoid.powers r) m n g
  let eTop := KernelSections.specKernelSectionEquiv f ⊤
  let eMap : gU.ker ≃ₗ[R]
      (IsLocalizedModule.map (Submonoid.powers r) m n g).ker :=
    LinearEquiv.ofEq _ _ (congrArg LinearMap.ker hmap.symm)
  let eU := KernelSections.specKernelSectionEquiv f U ≪≫ₗ eMap
  let a : Γ(kernel f, ⊤) →ₗ[R] Γ(kernel f, U) :=
    ((modulesSpecToSheaf.obj (kernel f)).obj.map U.leTop.op).hom
  have hsquare : eU.toLinearMap.comp a = k.comp eTop.toLinearMap := by
    ext x
    change (eMap (KernelSections.specKernelSectionEquiv f U (a x))).1 =
      m (KernelSections.specKernelSectionEquiv f ⊤ x).1
    change (KernelSections.specKernelSectionEquiv f U (a x)).1 =
      m (KernelSections.specKernelSectionEquiv f ⊤ x).1
    rw [KernelSections.specKernelSectionEquiv_coe, KernelSections.specKernelSectionEquiv_coe]
    exact ConcreteCategory.congr_hom
      ((kernel.ι f).val.naturality U.leTop.op) x
  let : Module Γ(Spec R, U)
      ((modulesSpecToSheaf.obj M).obj.obj (op U)) :=
    (inferInstance : Module Γ(Spec R, U) Γ(M, U))
  let : IsScalarTower R Γ(Spec R, U)
      ((modulesSpecToSheaf.obj M).obj.obj (op U)) :=
    (inferInstance : IsScalarTower R Γ(Spec R, U) Γ(M, U))
  let : Module Γ(Spec R, U)
      ((modulesSpecToSheaf.obj N).obj.obj (op U)) :=
    (inferInstance : Module Γ(Spec R, U) Γ(N, U))
  let : IsScalarTower R Γ(Spec R, U)
      ((modulesSpecToSheaf.obj N).obj.obj (op U)) :=
    (inferInstance : IsScalarTower R Γ(Spec R, U) Γ(N, U))
  have hk : IsLocalizedModule.Away r k :=
    LinearMap.toKerLocalized_isLocalizedModule
      (S := Γ(Spec R, U)) (Submonoid.powers r) m n g
  exact (Localized.ModuleSquares.isLocalizedModule_iff_of_linearEquiv_square
    (Submonoid.powers r) a k eTop eU hsquare).mpr hk

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.QuasicoherentKernels
