import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.SubgroupTransport
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base

/-! # Image Comparison -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison

noncomputable section

/-! Passage to the actual parameter scheme preserves subgroup images,
including the complete functor of an embedded kernel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Kernel.Base
attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup

universe u

variable {S : Scheme.{u}} (G H : Grp (Over S)) (P : Over S)
  (f : G ⟶ H) (F : AbelianScheme.TorsionQuotient.SubgroupFunctor.RelativeSubgroup G.X P)

theorem relativeParameter_image_comparison :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage ((Over.pullback P.hom).mapGrp.map f).hom.hom
        (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) =
      AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H P (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage f.hom.hom F) := by
  ext U t y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm x, hx, ?_⟩
    exact (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom f U x).symm
  · rintro ⟨x, hx, hxy⟩
    change x ∈ F.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U) at hx
    change x ≫ f.hom.hom = (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm y at hxy
    refine ⟨AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U x, ?_, ?_⟩
    · change (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U).symm
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U x) ∈
          F.points ((Over.map P.hom).obj U) (AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.parameterBasePoint P U)
      exact (MulEquiv.symm_apply_apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U) x).symm ▸ hx
    · apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom H U).symm.injective
      exact (AbelianScheme.CartierDuality.EvaluationBaseChange.Construction.Schemes.pullbackPointMulEquiv_symm_comp P.hom f U
        (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U x)).trans
        ((congrArg (fun z => z ≫ f.hom.hom)
          (MulEquiv.symm_apply_apply (AbelianScheme.CartierDuality.CharacterBaseChange.Construction.Schemes.pullbackPointMulEquiv P.hom G U) x)).trans hxy)

theorem fixedKernelFamily_image {S : Scheme.{u}} {A B C P : Over S}
    [GrpObj A] [GrpObj B] [GrpObj C]
    (f : A ⟶ B) (g : B ⟶ C) [IsMonHom f] [IsMonHom g] :
    AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage g (Kernel.Base.fixedKernelFamily (P := P) f) =
      Kernel.Base.fixedKernelFamily (P := P) (f ≫ g) := by
  ext U t z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, show x ≫ (f ≫ g) = (x ≫ f) ≫ g from (Category.assoc x f g).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x ≫ f, ⟨x, rfl⟩, show (x ≫ f) ≫ g = x ≫ (f ≫ g) from Category.assoc x f g⟩

local instance pulledBackHom : IsMonHom ((Over.pullback P.hom).map f.hom.hom) :=
  Functor.map.instIsMonHom (F := Over.pullback P.hom) (f := f.hom.hom) G.X H.X

theorem parameter_kernel_image {K : Over P.left} [GrpObj K]
    (k : K ⟶ (Over.pullback P.hom).obj G.X) [IsMonHom k]
    (hk : Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 P.left)) k = AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter G P F) :
    Kernel.Base.fixedKernelFamily (P := Over.mk (𝟙 P.left))
      (k ≫ (Over.pullback P.hom).map f.hom.hom) =
        AbelianScheme.IsogenyQuotient.Relative.ParameterBaseChange.Construction.relativeSubgroupOverParameter H P (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage f.hom.hom F) :=
  (fixedKernelFamily_image k ((Over.pullback P.hom).map f.hom.hom)).symm.trans
    ((congrArg (AbelianScheme.IsogenyQuotient.SubgroupTransport.Construction.relativeSubgroupImage ((Over.pullback P.hom).map f.hom.hom)) hk).trans
      (relativeParameter_image_comparison G H P f F))

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.ImageComparison
