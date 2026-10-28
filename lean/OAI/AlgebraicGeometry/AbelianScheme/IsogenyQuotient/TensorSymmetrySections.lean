import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TrilinearProducts

/-! # Tensor Symmetry Sections -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction

noncomputable section

/-! The symmetry of the actual sheaf tensor product exchanges the
two inputs of its universal bilinear map on sections. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

local instance tensorSectionPresheafMonoidal (X : Scheme.{u}) : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

local instance tensorSectionPresheafSymmetric (X : Scheme.{u}) : SymmetricCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)

variable {X : Scheme.{u}} (M N : X.Modules)

set_option backward.isDefEq.respectTransparency false in
theorem tensorModuleCommIso_bilinear :
    AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N M) (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).hom =
      BilinearFlip.Construction.flipLineBilinear (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear N M) := by
  have hu : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv M N (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule N M) (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).hom =
      (CategoryTheory.BraidedCategory.braiding M.val N.val).hom ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) N.val M.val) := by
    exact ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (CategoryTheory.BraidedCategory.braiding M.val N.val).hom).symm
  refine (congrArg AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom hu).trans ?_
  ext U m n
  rfl

theorem tensorModuleCommIso_app_tensor (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).hom.app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n) =
      (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear N M).app U n m := by
  have h := tensorModuleCommIso_bilinear M N
  rw [Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear_postcomp] at h
  exact congrArg (fun b => b.app U m n) h

theorem tensorModuleCommIso_inv_app_tensor (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).inv.app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear N M).app U n m) =
      (Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n := by
  have h := congrArg (fun v => (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).inv.app U v)
    (tensorModuleCommIso_app_tensor M N U m n)
  exact h.symm.trans (congrArg (fun f => f.app U ((Picard.Homomorphisms.TensorAssociativity.Construction.tensorModuleBilinear M N).app U m n))
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleCommIso M N).hom_inv_id)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TensorSymmetrySections.Construction
