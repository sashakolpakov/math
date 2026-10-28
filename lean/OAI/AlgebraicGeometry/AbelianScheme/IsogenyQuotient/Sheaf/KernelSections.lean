import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels

/-! # Kernel Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.KernelSections.Construction

noncomputable section

/-!
Sections of an actual commutative fppf-sheaf kernel are exactly the
kernel of the original map on sections. The comparison preserves the
kernel inclusion, so it can detect the literal annihilator subgroup.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.SheafKernels.Construction

universe u

variable {S : Scheme.{u}} {F G : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (f : F ⟶ G) (T : Over S)

def sheafKernelSectionsEquiv :
    (kernel f).obj.obj (.op T) ≃* (f.hom.app (.op T)).hom.ker := by
  let V := sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} ⋙
    (evaluation (Over S)ᵒᵖ CommGrpCat.{u + 1}).obj (.op T)
  let h := (isLimitMapConeForkEquiv' V (kernel.condition f)).toFun
    (isLimitOfPreserves V (kernelIsKernel f))
  exact (h.conePointUniqueUpToIso (CartierDuality.SheafKernels.Construction.CommutativeSheaves.kernelIsLimit (V.map f))).commGroupIsoToMulEquiv

theorem sheafKernelSectionsEquiv_val (x : (kernel f).obj.obj (.op T)) :
    (sheafKernelSectionsEquiv f T x).val = (kernel.ι f).hom.app (.op T) x := by
  let V := sheafToPresheaf (Scheme.fppfTopology.over S) CommGrpCat.{u + 1} ⋙
    (evaluation (Over S)ᵒᵖ CommGrpCat.{u + 1}).obj (.op T)
  let h := (isLimitMapConeForkEquiv' V (kernel.condition f)).toFun
    (isLimitOfPreserves V (kernelIsKernel f))
  exact ConcreteCategory.congr_hom
    (h.conePointUniqueUpToIso_hom_comp (CartierDuality.SheafKernels.Construction.CommutativeSheaves.kernelIsLimit (V.map f)) WalkingParallelPair.zero) x

theorem sheafKernel_sections_range :
    ((kernel.ι f).hom.app (.op T)).hom.range = (f.hom.app (.op T)).hom.ker := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [← sheafKernelSectionsEquiv_val]
    exact (sheafKernelSectionsEquiv f T y).property
  · intro hx
    refine ⟨(sheafKernelSectionsEquiv f T).symm ⟨x, hx⟩, ?_⟩
    rw [← sheafKernelSectionsEquiv_val, MulEquiv.apply_symm_apply]

def sheafSubobjectSections (J : Subobject F) : Subgroup (F.obj.obj (.op T)) :=
  (J.arrow.hom.app (.op T)).hom.range

theorem sheafSubobjectSections_kernel :
    sheafSubobjectSections T (kernelSubobject f) = (f.hom.app (.op T)).hom.ker := by
  rw [← sheafKernel_sections_range]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(kernelSubobjectIso f).hom.hom.app (.op T) y, ?_⟩
    have h := congrArg (fun k => k.hom.app (.op T) y) (kernelSubobject_arrow f)
    exact h.trans hy
  · rintro ⟨y, hy⟩
    refine ⟨(kernelSubobjectIso f).inv.hom.app (.op T) y, ?_⟩
    have h := congrArg (fun k => k.hom.app (.op T) y) (kernelSubobject_arrow' f)
    exact h.trans hy

theorem sheafSubobjectSections_mk {H : CartierDuality.CommutativeSheavesAb.Construction.Schemes.FppfAb S} (i : H ⟶ F) [Mono i] :
    sheafSubobjectSections T (Subobject.mk i) = (i.hom.app (.op T)).hom.range := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨(Subobject.underlyingIso i).hom.hom.app (.op T) y, ?_⟩
    have h := congrArg (fun k => k.hom.app (.op T) y) (Subobject.underlyingIso_hom_comp_eq_mk i)
    exact h.trans hy
  · rintro ⟨y, hy⟩
    refine ⟨(Subobject.underlyingIso i).inv.hom.app (.op T) y, ?_⟩
    have h := congrArg (fun k => k.hom.app (.op T) y) (Subobject.underlyingIso_arrow i)
    exact h.trans hy

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Sheaf.KernelSections.Construction
