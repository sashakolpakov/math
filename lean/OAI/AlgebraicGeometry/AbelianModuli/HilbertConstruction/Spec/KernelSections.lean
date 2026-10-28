/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SchemeModuleQuasicoherent.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Kernel Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.KernelSections

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules Opposite

universe u

variable {R : CommRingCat.{u}}

local instance evaluationAdditive (U : (Spec R).Opens) :
    (SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)).Additive := by
  dsimp only [SheafOfModules.evaluation]
  infer_instance

def specKernelSectionEquiv
    {M N : (Spec R).Modules} (f : M ⟶ N) (U : (Spec R).Opens) :
    Γ(kernel f, U) ≃ₗ[R]
      ((modulesSpecToSheaf.map f).hom.app (op U)).hom.ker :=
  let e := (PreservesKernel.iso
    (SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)) f).trans
      (ModuleCat.kernelIsoKer _)
  let fU : Γ(M, U) →ₗ[Γ(Spec R, U)] Γ(N, U) :=
    (f.val.app (op U)).hom
  letI : Module R fU.ker :=
    Module.compHom (R := Γ(Spec R, U)) fU.ker
      (algebraMap R Γ(Spec R, U))
  letI : IsScalarTower R Γ(Spec R, U) fU.ker :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  let eΓ : Γ(kernel f, U) ≃ₗ[Γ(Spec R, U)] fU.ker :=
    e.toLinearEquiv
  let eR : Γ(kernel f, U) ≃ₗ[R] fU.ker :=
    { toEquiv := eΓ.toEquiv
      map_add' := eΓ.map_add
      map_smul' := by
        intro r x
        change eΓ ((algebraMap R Γ(Spec R, U)) r • x) =
          (algebraMap R Γ(Spec R, U)) r • eΓ x
        exact eΓ.map_smul _ _ }
  let eKer : fU.ker ≃ₗ[R]
      ((modulesSpecToSheaf.map f).hom.app (op U)).hom.ker :=
    { toFun := fun x ↦ ⟨x.1, x.2⟩
      invFun := fun x ↦ ⟨x.1, x.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := by
        intro r x
        apply Subtype.ext
        change (algebraMap R Γ(Spec R, U)) r • (x : Γ(M, U)) = _
        rfl }
  eR.trans eKer

theorem specKernelSectionEquiv_coe
    {M N : (Spec R).Modules} (f : M ⟶ N) (U : (Spec R).Opens)
    (x : Γ(kernel f, U)) :
    (specKernelSectionEquiv f U x).1 =
      (kernel.ι f).val.app (op U) x := by
  change (((ModuleCat.kernelIsoKer
      ((SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)).map f)).hom
        ((PreservesKernel.iso
          (SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)) f).hom x)).1) =
      (kernel.ι f).val.app (op U) x
  let F := SheafOfModules.evaluation (Spec R).ringCatSheaf (op U)
  have hsub := ConcreteCategory.congr_hom
    (ModuleCat.kernelIsoKer_hom_ker_subtype (F.map f))
    ((PreservesKernel.iso F f).hom x)
  have hcomparison := ConcreteCategory.congr_hom
    (PreservesKernel.iso_inv_ι (G := F) (f := f))
    ((PreservesKernel.iso F f).hom x)
  change F.map (kernel.ι f)
      ((PreservesKernel.iso F f).inv ((PreservesKernel.iso F f).hom x)) =
    (kernel.ι (F.map f)) ((PreservesKernel.iso F f).hom x) at hcomparison
  have hinv : (PreservesKernel.iso F f).inv
      ((PreservesKernel.iso F f).hom x) = x :=
    ConcreteCategory.congr_hom (PreservesKernel.iso F f).hom_inv_id x
  rw [hinv] at hcomparison
  symm at hcomparison
  exact hsub.trans hcomparison

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Spec.KernelSections
