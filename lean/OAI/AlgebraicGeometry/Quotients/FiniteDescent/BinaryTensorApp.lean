import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorPrecomp
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units

/-! # Binary Tensor App -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorApp.Construction.BinaryTensorUnit

noncomputable section

/-! Coordinates of binary tensor sections in the structure-sheaf frame. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units

universe u

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

theorem unitLeft_app (M : X.Modules) (U : X.Opens) (r : Γ(X, U)) (s : Γ(M, U)) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom.app U
      ((BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M).app U r s) = r • s := by
  have he : AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom =
      (λ_ M.val).hom :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).homEquiv _ M |>.apply_symm_apply (λ_ M.val).hom
  have h := congrArg (fun β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M => β.app U r s)
    (BinaryTensorPrecomp.Construction.BinaryTensorUniversal.postcomp (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom)
  change _ = (AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ofTensorPresheafHom
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleHomEquiv (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M M (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom)).app U r s at h
  rw [he] at h
  exact h

theorem unitLeft_inv_app (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv.app U s =
      (BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) M).app U (1 : Γ(X, U)) s := by
  apply ((ConcreteCategory.isIso_iff_bijective ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom.app U)).mp
    inferInstance).1
  have he := ConcreteCategory.congr_hom
    (congrArg (fun a : M ⟶ M => a.app U) (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv_hom_id) s
  change (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).hom.app U ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso M).inv.app U s) = s at he
  rw [he, unitLeft_app, one_smul]

theorem tensorSection_app {M N : X.Modules} (s : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ M)
    (t : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X ⟶ N) (U : X.Opens) (r : Γ(X, U)) :
    (BinaryTensorId.Construction.BinaryTensorMap.tensorSection s t).app U r =
      (BinaryTensorPrecomp.Construction.BinaryTensorUniversal.bilinear M N).app U
        (s.app U (1 : Γ(X, U))) (t.app U r) := by
  change (BinaryTensorId.Construction.BinaryTensorMap.map s t).app U ((AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).inv.app U r) = _
  rw [unitLeft_inv_app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U r]
  exact congrArg (fun β : AbelianModuli.HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule M N) => β.app U (1 : Γ(X, U)) r) (BinaryTensorPrecomp.Construction.BinaryTensorUniversal.map_spec s t)

theorem unit_conjugation (a b : End (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)) :
    (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).inv ≫ BinaryTensorId.Construction.BinaryTensorMap.map a b ≫
      (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom = a ≫ b := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  change (AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModuleUnitLeftIso (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X)).hom.app U
    ((BinaryTensorId.Construction.BinaryTensorMap.tensorSection a b).app U r) = b.app U (a.app U r)
  rw [tensorSection_app, unitLeft_app (AbelianModuli.HilbertConstruction.Line.Bundles.structureModule X) U
    (show Γ(X, U) from a.app U (1 : Γ(X, U))) (b.app U r)]
  change (show Γ(X, U) from a.app U (1 : Γ(X, U))) * (show Γ(X, U) from b.app U r) = _
  rw [AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app b U r, AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app b U (a.app U r),
    AbelianModuli.HilbertConstruction.TensorPower.Units.structureModuleEnd_app a U r]
  let ca : Γ(X, U) := a.app U (1 : Γ(X, U))
  let cb : Γ(X, U) := b.app U (1 : Γ(X, U))
  change ca * (r * cb) = (r * ca) * cb
  exact (mul_left_comm _ _ _).trans (mul_assoc _ _ _).symm

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorApp.Construction.BinaryTensorUnit
