import OAI.Analysis.DifferentialForms.Manifold.LocallyConstantKernel
import OAI.Analysis.DifferentialForms.Manifold.CochainAugmentation
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare
import OAI.AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant

/-! # De Rham Resolution -/

namespace OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution

noncomputable section

/-!
# The genuine de Rham sheaf resolution on a smooth real manifold

The independently defined locally constant sheaf is the proved kernel in
degree zero. The proved manifold Poincare theorem supplies positive exactness.
Thus the explicit coefficient inclusion is a quasi-isomorphism of actual
complexes of sheaves. No statement about ordinary global sections preserving
this quasi-isomorphism is made.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

attribute [local instance] AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives.manifoldSheafPreadditive
attribute [local instance] AlgebraicTopology.DeRham.Comparison.ManifoldSheafLocalPrimitives.manifoldSheafCategoryWithHomology

universe u

/-- The actual single-object locally constant coefficient complex has homology.
This explicit instance preserves the zero-morphism structure of the manifold API. -/
instance locallyConstantSheafSingle_hasHomology (X : TopCat.{u}) (n : ℕ) :
    ((CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{u} ℂ) X)).obj
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X)).HasHomology n := by
  infer_instance

variable (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  (M : Type u) [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual locally constant inclusion kills the complex's first differential. -/
theorem manifoldLocallyConstantToDeRham_comp_d :
    LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M ≫ (SheafDeRham.manifoldDeRhamSheafComplex E M).d 0 1 = 0 := by
  rw [SheafDeRham.manifoldDeRhamSheafComplex_d]
  exact LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf_comp_d E M

/-- The explicit locally constant coefficient map into the actual manifold de Rham complex. -/
def manifoldLocallyConstantDeRhamAugmentation :
    (CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of M))).obj
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M)) ⟶ SheafDeRham.manifoldDeRhamSheafComplex E M :=
  (CochainComplex.fromSingle₀Equiv (SheafDeRham.manifoldDeRhamSheafComplex E M)
    (AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf (TopCat.of M))).symm
      ⟨LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M, manifoldLocallyConstantToDeRham_comp_d E M⟩

/-- The actual manifold de Rham complex with its coefficient sheaf inserted first. -/
def manifoldLocallyConstantAugmentedDeRhamComplex :
    CochainComplex (TopCat.Sheaf (ModuleCat.{u} ℂ) (TopCat.of M)) ℕ :=
  (SheafDeRham.manifoldDeRhamSheafComplex E M).augment (LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M)
    (manifoldLocallyConstantToDeRham_comp_d E M)

/-- Removing the coefficient term recovers the actual manifold de Rham complex. -/
def manifoldLocallyConstantAugmentedDeRhamTruncateIso :
    CochainComplex.truncate.obj (manifoldLocallyConstantAugmentedDeRhamComplex E M) ≅
      SheafDeRham.manifoldDeRhamSheafComplex E M := CochainComplex.truncateAugment _ _ _

/-- The proved kernel theorem, expressed using the actual complex differential. -/
def manifoldLocallyConstantToDeRhamKernelIsLimit :
    IsLimit (KernelFork.ofι (LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M)
      (manifoldLocallyConstantToDeRham_comp_d E M)) := by
  refine IsKernel.ofIso (ManifoldSheaf.manifoldFormSheafD E M 0)
    (LocallyConstantKernel.manifoldLocallyConstantSheafKernelIsLimit E M) _
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_
  · rw [SheafDeRham.manifoldDeRhamSheafComplex_d]
    rfl
  · rfl

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- The locally constant augmentation is an acyclic complex of actual manifold sheaves. -/
theorem manifoldLocallyConstantAugmentedDeRham_acyclic :
    (manifoldLocallyConstantAugmentedDeRhamComplex E M).Acyclic :=
  CochainAugmentation.cochainAugment_acyclic_of_kernel (SheafDeRham.manifoldDeRhamSheafComplex E M)
    (LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) (manifoldLocallyConstantToDeRham_comp_d E M)
    (manifoldLocallyConstantToDeRhamKernelIsLimit E M)
    (AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare.manifoldDeRhamSheafComplex_exactAt_succ E M)

/-- The explicit coefficient inclusion is a quasi-isomorphism on the actual manifold. -/
theorem manifoldLocallyConstantDeRhamAugmentation_quasiIso :
    QuasiIso (manifoldLocallyConstantDeRhamAugmentation E M) :=
  CochainAugmentation.cochainAugmentation_quasiIso (SheafDeRham.manifoldDeRhamSheafComplex E M)
    (LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E M) (manifoldLocallyConstantToDeRham_comp_d E M)
    (manifoldLocallyConstantToDeRhamKernelIsLimit E M)
    (AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare.manifoldDeRhamSheafComplex_exactAt_succ E M)

end FiniteDimensional

/-- Mathlib's standard constant complex sheaf on an arbitrary small topological space. -/
def constantComplexSheafOn (X : TopCat.{0}) : TopCat.Sheaf (ModuleCat.{0} ℂ) X :=
  (constantSheaf (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)).obj (ModuleCat.of ℂ ℂ)

/-- The actual standard-constant coefficient complex has homology in every degree. -/
instance constantComplexSheafSingle_hasHomology (X : TopCat.{0}) (n : ℕ) :
    ((CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{0} ℂ) X)).obj
      (constantComplexSheafOn X)).HasHomology n := by
  infer_instance

/-- The proved identification of standard constant coefficients with locally constant sections. -/
def constantComplexLocallyConstantIsoOn (X : TopCat.{0}) :
    constantComplexSheafOn X ≅ AlgebraicTopology.DeRham.Comparison.LocallyConstantSheaf.locallyConstantSheaf X := AlgebraicTopology.DeRham.Comparison.ConstantLocallyConstant.constantSheafLocallyConstantIso X

variable (N : Type) [TopologicalSpace N] [ChartedSpace E N]
  [IsManifold 𝓘(ℝ, E) ∞ N]

/-- The standard constant sheaf maps by the actual scalar inclusion into manifold zero-forms. -/
def manifoldConstantToDeRham :
    constantComplexSheafOn (TopCat.of N) ⟶ (SheafDeRham.manifoldDeRhamSheafComplex E N).X 0 :=
  (constantComplexLocallyConstantIsoOn (TopCat.of N)).hom ≫
    LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E N

theorem manifoldConstantToDeRham_comp_d :
    manifoldConstantToDeRham E N ≫ (SheafDeRham.manifoldDeRhamSheafComplex E N).d 0 1 = 0 := by
  change ((constantComplexLocallyConstantIsoOn (TopCat.of N)).hom ≫
    LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E N) ≫ (SheafDeRham.manifoldDeRhamSheafComplex E N).d 0 1 = 0
  rw [SheafDeRham.manifoldDeRhamSheafComplex_d]
  change (((constantComplexLocallyConstantIsoOn (TopCat.of N)).hom ≫
    LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E N) ≫ ManifoldSheaf.manifoldFormSheafD E N 0 :
      constantComplexSheafOn (TopCat.of N) ⟶ ManifoldSheaf.manifoldFormSheaf E N 1) = 0
  rw [Category.assoc, LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf_comp_d, comp_zero]

/-- The standard constant coefficient object is the actual kernel of the first differential. -/
def manifoldConstantToDeRhamKernelIsLimit :
    IsLimit (KernelFork.ofι (manifoldConstantToDeRham E N)
      (manifoldConstantToDeRham_comp_d E N)) := by
  refine IsLimit.ofIsoLimit (manifoldLocallyConstantToDeRhamKernelIsLimit E N) ?_
  refine Fork.ext (constantComplexLocallyConstantIsoOn (TopCat.of N)).symm ?_
  change (constantComplexLocallyConstantIsoOn (TopCat.of N)).inv ≫
      ((constantComplexLocallyConstantIsoOn (TopCat.of N)).hom ≫
        LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E N) = LocallyConstantKernel.manifoldLocallyConstantToZeroSheaf E N
  rw [Iso.inv_hom_id_assoc]

/-- The actual standard constant-sheaf augmentation of the manifold de Rham complex. -/
def manifoldDeRhamSheafAugmentation :
    (CochainComplex.single₀ (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of N))).obj
      (constantComplexSheafOn (TopCat.of N)) ⟶ SheafDeRham.manifoldDeRhamSheafComplex E N :=
  (CochainComplex.fromSingle₀Equiv (SheafDeRham.manifoldDeRhamSheafComplex E N)
    (constantComplexSheafOn (TopCat.of N))).symm
      ⟨manifoldConstantToDeRham E N, manifoldConstantToDeRham_comp_d E N⟩

/-- The augmented complex begins with the standard constant complex sheaf. -/
def manifoldAugmentedDeRhamSheafComplex :
    CochainComplex (TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of N)) ℕ :=
  (SheafDeRham.manifoldDeRhamSheafComplex E N).augment (manifoldConstantToDeRham E N)
    (manifoldConstantToDeRham_comp_d E N)

/-- Truncation removes exactly the inserted coefficient term. -/
def manifoldAugmentedDeRhamSheafTruncateIso :
    CochainComplex.truncate.obj (manifoldAugmentedDeRhamSheafComplex E N) ≅
      SheafDeRham.manifoldDeRhamSheafComplex E N := CochainComplex.truncateAugment _ _ _

variable [FiniteDimensional ℝ E]

/-- The actual constant-complex-sheaf augmentation is an exact manifold de Rham resolution. -/
theorem manifoldAugmentedDeRhamSheaf_acyclic :
    (manifoldAugmentedDeRhamSheafComplex E N).Acyclic :=
  CochainAugmentation.cochainAugment_acyclic_of_kernel (SheafDeRham.manifoldDeRhamSheafComplex E N)
    (manifoldConstantToDeRham E N) (manifoldConstantToDeRham_comp_d E N)
    (manifoldConstantToDeRhamKernelIsLimit E N)
    (AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare.manifoldDeRhamSheafComplex_exactAt_succ E N)

/-- The standard constant complex sheaf maps quasi-isomorphically to the genuine
de Rham sheaf complex on the smooth manifold. -/
theorem manifoldDeRhamSheafAugmentation_quasiIso :
    QuasiIso (manifoldDeRhamSheafAugmentation E N) :=
  CochainAugmentation.cochainAugmentation_quasiIso (SheafDeRham.manifoldDeRhamSheafComplex E N)
    (manifoldConstantToDeRham E N) (manifoldConstantToDeRham_comp_d E N)
    (manifoldConstantToDeRhamKernelIsLimit E N)
    (AlgebraicTopology.DeRham.Comparison.ManifoldSheafPoincare.manifoldDeRhamSheafComplex_exactAt_succ E N)

end

end OAI.Analysis.DifferentialForms.Manifold.DeRhamResolution
