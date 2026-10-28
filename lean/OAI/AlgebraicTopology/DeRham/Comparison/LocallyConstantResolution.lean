import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf
import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms
import OAI.AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant
import OAI.Analysis.DifferentialForms.Manifold.SmoothFormD
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Locally Constant Resolution -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantResolution

noncomputable section

/-!
# The first exact step of the de Rham sheaf resolution

The locally constant sheaf maps to the actual smooth zero-form sheaf. This
map is proved to be the categorical kernel of exterior differentiation.
The sheaf of locally constant functions was constructed independently of
forms, so the kernel identification is a theorem, not a definition.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace Opposite

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The explicit inclusion of locally constant sections into smooth zero-forms. -/
def locallyConstantToSmoothZeroPresheaf :
    LocallyConstantSheaf.locallyConstantPresheaf (TopCat.of E) ⟶ Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheaf E 0 where
  app U := ModuleCat.ofHom (LocallyConstantZeroForms.locallyConstantToZeroForm U.unop)
  naturality U V i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro f
    exact (LocallyConstantZeroForms.restrict_locallyConstantToZeroForm (leOfHom i.unop) f).symm

/-- Exterior differentiation kills the explicit locally constant inclusion. -/
theorem locallyConstantToSmoothZeroPresheaf_comp_d :
    locallyConstantToSmoothZeroPresheaf E ≫ Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheafD E 0 = 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  exact LocallyConstantZeroForms.d_locallyConstantToZeroForm U.unop f

/-- The same actual inclusion, regarded as a morphism of genuine sheaves. -/
def locallyConstantToSmoothZeroSheaf :
    LocallyConstantSheaf.locallyConstantSheaf (TopCat.of E) ⟶ Analysis.DifferentialForms.Manifold.SmoothFormD.smoothFormSheaf E 0 :=
  ObjectProperty.homMk (locallyConstantToSmoothZeroPresheaf E)

theorem locallyConstantToSmoothZeroSheaf_comp_d :
    locallyConstantToSmoothZeroSheaf E ≫ Analysis.DifferentialForms.Manifold.SmoothFormD.smoothFormSheafD E 0 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  exact locallyConstantToSmoothZeroPresheaf_comp_d E

/-- Sectionwise exactness is sufficient to prove the presheaf kernel universal property. -/
def locallyConstantPresheafKernelIsLimit :
    IsLimit (KernelFork.ofι (locallyConstantToSmoothZeroPresheaf E)
      (locallyConstantToSmoothZeroPresheaf_comp_d E)) := by
  apply evaluationJointlyReflectsLimits
  intro U
  refine (isLimitMapConeForkEquiv'
    ((evaluation (Opens (TopCat.of E))ᵒᵖ (ModuleCat.{u} ℂ)).obj U)
      (locallyConstantToSmoothZeroPresheaf_comp_d E)).symm ?_
  change IsLimit (KernelFork.ofι
    (f := (Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheafD E 0).app U)
    ((locallyConstantToSmoothZeroPresheaf E).app U) _)
  apply ModuleCat.isLimitKernelFork
    ((locallyConstantToSmoothZeroPresheaf E).app U)
    ((Analysis.DifferentialForms.Manifold.Presheaf.smoothFormPresheafD E 0).app U)
  · rw [LinearMap.exact_iff]
    exact (LocallyConstantZeroForms.range_locallyConstantToZeroForm U.unop).symm
  · exact LocallyConstantZeroForms.locallyConstantToZeroForm_injective U.unop

/-- The independently defined locally constant sheaf is the categorical kernel
of the actual degree-zero exterior derivative. -/
def locallyConstantSheafKernelIsLimit :
    IsLimit (KernelFork.ofι (locallyConstantToSmoothZeroSheaf E)
      (locallyConstantToSmoothZeroSheaf_comp_d E)) := by
  let F := TopCat.Sheaf.forget (ModuleCat.{u} ℂ) (TopCat.of E)
  apply isLimitOfReflects F
  refine (isLimitMapConeForkEquiv' F (locallyConstantToSmoothZeroSheaf_comp_d E)).symm ?_
  exact locallyConstantPresheafKernelIsLimit E

variable (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The standard constant complex sheaf, with the topological-sheaf wrapper explicit. -/
abbrev constantComplexSheaf : TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of V) :=
  (constantSheaf (Opens.grothendieckTopology (TopCat.of V)) (ModuleCat.{0} ℂ)).obj
    (ModuleCat.of ℂ ℂ)

/-- The proved constant-sheaf identification in the topological-sheaf category. -/
def constantComplexLocallyConstantIso :
    constantComplexSheaf V ≅ LocallyConstantSheaf.locallyConstantSheaf (TopCat.of V) :=
  ConstantLocallyConstant.constantSheafLocallyConstantIso (TopCat.of V)

/-- The canonical augmentation from mathlib's constant complex sheaf to smooth zero-forms. -/
def constantComplexToSmoothZeroSheaf :
    constantComplexSheaf V ⟶ Analysis.DifferentialForms.Manifold.SmoothFormD.smoothFormSheaf V 0 :=
  (constantComplexLocallyConstantIso V).hom ≫
    locallyConstantToSmoothZeroSheaf V

theorem constantComplexToSmoothZeroSheaf_comp_d :
    constantComplexToSmoothZeroSheaf V ≫ Analysis.DifferentialForms.Manifold.SmoothFormD.smoothFormSheafD V 0 = 0 := by
  simp only [constantComplexToSmoothZeroSheaf, Category.assoc,
    locallyConstantToSmoothZeroSheaf_comp_d, comp_zero]

/-- The actual constant complex sheaf is the categorical kernel of the actual
degree-zero exterior derivative. This uses the proved constant-sheaf identification. -/
def constantComplexSheafKernelIsLimit :
    IsLimit (KernelFork.ofι (constantComplexToSmoothZeroSheaf V)
      (constantComplexToSmoothZeroSheaf_comp_d V)) := by
  refine IsLimit.ofIsoLimit (locallyConstantSheafKernelIsLimit V) ?_
  refine Fork.ext (constantComplexLocallyConstantIso V).symm ?_
  simp [constantComplexToSmoothZeroSheaf]

end

end OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantResolution
