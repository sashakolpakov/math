import OAI.Analysis.DifferentialForms.Manifold.LocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.ManifoldSheaf
import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Locally Constant Kernel -/

namespace OAI.Analysis.DifferentialForms.Manifold.LocallyConstantKernel

noncomputable section

/-!
# The actual locally constant kernel of the manifold zero-form differential

The locally constant sheaf is defined independently of differential forms.
Its explicit inclusion is proved to satisfy the categorical kernel universal
property using the established sectionwise image/kernel equality.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite
open scoped _root_.Manifold ContDiff

open OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf

universe u

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual inclusion of locally constant sections into manifold zero-forms. -/
def manifoldLocallyConstantToZeroPresheaf :
    AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantPresheaf (TopCat.of M) ⟶ ManifoldSheaf.manifoldFormPresheaf E M 0 where
  app U := ModuleCat.ofHom (LocallyConstant.locallyConstantToManifoldZeroForm E U.unop)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (LocallyConstant.restrict_locallyConstantToManifoldZeroForm (E := E) (leOfHom i.unop) f).symm

/-- Exterior differentiation kills the actual locally constant inclusion. -/
theorem manifoldLocallyConstantToZeroPresheaf_comp_d :
    manifoldLocallyConstantToZeroPresheaf E M ≫ ManifoldSheaf.manifoldFormPresheafD E M 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact LocallyConstant.d_locallyConstantToManifoldZeroForm (E := E) U.unop f

/-- The same inclusion between the independently constructed genuine sheaves. -/
def manifoldLocallyConstantToZeroSheaf :
    AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M) ⟶ ManifoldSheaf.manifoldFormSheaf E M 0 :=
  ObjectProperty.homMk (manifoldLocallyConstantToZeroPresheaf E M)

theorem manifoldLocallyConstantToZeroSheaf_comp_d :
    manifoldLocallyConstantToZeroSheaf E M ≫ ManifoldSheaf.manifoldFormSheafD E M 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  exact manifoldLocallyConstantToZeroPresheaf_comp_d E M

/-- The sectionwise image/kernel equality gives the presheaf kernel universal property. -/
def manifoldLocallyConstantPresheafKernelIsLimit :
    IsLimit (KernelFork.ofι (manifoldLocallyConstantToZeroPresheaf E M)
      (manifoldLocallyConstantToZeroPresheaf_comp_d E M)) := by
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConeForkEquiv'
    ((evaluation (Opens (TopCat.of M))ᵒᵖ (ModuleCat.{u} ℂ)).obj U)
      (manifoldLocallyConstantToZeroPresheaf_comp_d E M)).symm ?_
  change IsLimit (KernelFork.ofι
    (f := (ManifoldSheaf.manifoldFormPresheafD E M 0).app U)
    ((manifoldLocallyConstantToZeroPresheaf E M).app U) _)
  apply ModuleCat.isLimitKernelFork
    ((manifoldLocallyConstantToZeroPresheaf E M).app U)
    ((ManifoldSheaf.manifoldFormPresheafD E M 0).app U)
  · rw [LinearMap.exact_iff]
    exact (LocallyConstant.range_locallyConstantToManifoldZeroForm (E := E) U.unop).symm
  · exact LocallyConstant.locallyConstantToManifoldZeroForm_injective (E := E) U.unop

/-- The genuine locally constant sheaf is the kernel of the actual manifold d0. -/
def manifoldLocallyConstantSheafKernelIsLimit :
    IsLimit (KernelFork.ofι (manifoldLocallyConstantToZeroSheaf E M)
      (manifoldLocallyConstantToZeroSheaf_comp_d E M)) := by
  let F := TopCat.Sheaf.forget (ModuleCat.{u} ℂ) (TopCat.of M)
  apply isLimitOfReflects F
  refine (isLimitMapConeForkEquiv' F
    (manifoldLocallyConstantToZeroSheaf_comp_d E M)).symm ?_
  exact manifoldLocallyConstantPresheafKernelIsLimit E M

end

end OAI.Analysis.DifferentialForms.Manifold.LocallyConstantKernel
