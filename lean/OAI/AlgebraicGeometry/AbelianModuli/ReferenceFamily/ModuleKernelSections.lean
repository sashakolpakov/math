import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleHomOf
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Module Kernel Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleKernelSections

noncomputable section

/-! Sections of an actual algebraic kernel sheaf are exactly the
kernel of the original map on sections, on every open subset. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

local instance (X : Scheme.{0}) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).PreservesZeroMorphisms := by
  unfold SheafOfModules.evaluation
  infer_instance

variable {X : Scheme.{0}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens)

def moduleSectionLinearMap : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := (f.val.app (op U)).hom

def moduleKernelSectionEquiv : Γ(kernel f, U) ≃ₗ[Γ(X, U)] (moduleSectionLinearMap f U).ker :=
  ((PreservesKernel.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) f) ≪≫
    ModuleCat.kernelIsoKer ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map f)).toLinearEquiv

theorem moduleKernelSectionEquiv_symm_inclusion (a : (moduleSectionLinearMap f U).ker) :
    (kernel.ι f).app U ((moduleKernelSectionEquiv f U).symm a) = a.val := by
  let G := SheafOfModules.evaluation X.ringCatSheaf (op U)
  have h : (ModuleCat.kernelIsoKer (G.map f)).inv ≫ (PreservesKernel.iso G f).inv ≫
      G.map (kernel.ι f) = ModuleCat.ofHom (G.map f).hom.ker.subtype := by
    exact (congrArg ((ModuleCat.kernelIsoKer (G.map f)).inv ≫ ·)
      (PreservesKernel.iso_inv_ι G f)).trans (ModuleCat.kernelIsoKer_inv_kernel_ι (G.map f))
  exact congrArg (fun q => q a) h

def moduleKernelSectionLift (a : Γ(M, U)) (ha : f.app U a = 0) : Γ(kernel f, U) :=
  (moduleKernelSectionEquiv f U).symm ⟨a, ha⟩

theorem moduleKernelSectionLift_inclusion (a : Γ(M, U)) (ha : f.app U a = 0) :
    (kernel.ι f).app U (moduleKernelSectionLift f U a ha) = a :=
  moduleKernelSectionEquiv_symm_inclusion f U ⟨a, ha⟩

theorem moduleKernel_inclusion_injective : Function.Injective ((kernel.ι f).app U) := by
  intro a b h
  apply (moduleKernelSectionEquiv f U).injective
  apply Subtype.ext
  have ha := moduleKernelSectionEquiv_symm_inclusion f U (moduleKernelSectionEquiv f U a)
  have hb := moduleKernelSectionEquiv_symm_inclusion f U (moduleKernelSectionEquiv f U b)
  rw [LinearEquiv.symm_apply_apply] at ha hb
  exact ha.symm.trans (h.trans hb)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ModuleKernelSections
