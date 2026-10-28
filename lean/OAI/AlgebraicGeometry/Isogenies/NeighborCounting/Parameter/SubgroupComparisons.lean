import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.KernelProducts
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison

/-! # Subgroup Comparisons -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons

noncomputable section

/-! The parameter comparison preserves the original embedded subgroup
and its inverse image, using the same actual pullback point maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Parameter.AnnihilatorComparison.Construction OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup AbelianScheme.IsogenyQuotient.PairingBaseChange.Construction.pulledbackGroup_commutative

universe u

variable {S : Scheme.{u}} (G H : Grp (Over S))
  (P : Over S) (i : G ⟶ H)

theorem relativeParameter_identity_kernel :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (Kernel.Base.fixedKernelFamily (𝟙 G.X)) =
      Kernel.Base.fixedKernelFamily (𝟙 ((Over.pullback P.hom).mapGrp.obj G).X) := by
  ext U t z
  constructor
  · intro _
    exact ⟨z, Category.comp_id z⟩
  · intro _
    change ∃ a : (Over.map P.hom).obj U ⟶ G.X,
      a ≫ 𝟙 G.X = (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm z
    exact ⟨(AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm z, Category.comp_id _⟩

theorem relativeParameter_fixed_kernel :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H P (Kernel.Base.fixedKernelFamily i.hom.hom) =
      Kernel.Base.fixedKernelFamily ((Over.pullback P.hom).mapGrp.map i).hom.hom := by
  have h := ImageComparison.relativeParameter_image_comparison G H P i (Kernel.Base.fixedKernelFamily (𝟙 G.X))
  simp only [relativeParameter_identity_kernel, ImageComparison.fixedKernelFamily_image, Category.id_comp] at h
  exact h.symm

theorem relativeParameter_pullback_comparison (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup H.X P) :
    AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback i.hom.hom F) =
      AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupPullback ((Over.pullback P.hom).mapGrp.map i).hom.hom
        (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H P F) := by
  ext U t z
  change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm z ≫ i.hom.hom ∈
      F.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) ↔
    (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm
      (z ≫ ((Over.pullback P.hom).mapGrp.map i).hom.hom) ∈
      F.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U)
  rw [AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp]

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.SubgroupComparisons
