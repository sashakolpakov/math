import OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Global Sections Kernel -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsKernel

noncomputable section

/-! The kernel universal property on actual global sections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem exists_globalSection_kernel_preimage {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (x : Γ(M, ⊤)) (hx : f.app ⊤ x = 0) :
    ∃ y : Γ(kernel f, ⊤), (kernel.ι f).app ⊤ y = x := by
  let g := (UnitHomTopSections.unitHomTopSectionsEquiv M).symm x
  have hg : g ≫ f = 0 := by
    apply (UnitHomTopSections.unitHomTopSectionsEquiv N).injective
    change UnitHomTopSections.unitHomTopSectionsEquiv N (g ≫ f) = 0
    rw [GlobalSectionsMono.unitHomTopSectionsEquiv_comp]
    exact (congrArg (f.app ⊤) ((UnitHomTopSections.unitHomTopSectionsEquiv M).apply_symm_apply x)).trans hx
  refine ⟨UnitHomTopSections.unitHomTopSectionsEquiv (kernel f) (kernel.lift f g hg), ?_⟩
  rw [← GlobalSectionsMono.unitHomTopSectionsEquiv_comp, kernel.lift_ι]
  exact (UnitHomTopSections.unitHomTopSectionsEquiv M).apply_symm_apply x

theorem globalSections_exact_kernel {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) :
    Function.Exact ((kernel.ι f).app ⊤) (f.app ⊤) := by
  intro x
  constructor
  · exact exists_globalSection_kernel_preimage f x
  · rintro ⟨y, rfl⟩
    change (kernel.ι f ≫ f).app ⊤ y = 0
    rw [kernel.condition]
    rfl

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.GlobalSectionsKernel
