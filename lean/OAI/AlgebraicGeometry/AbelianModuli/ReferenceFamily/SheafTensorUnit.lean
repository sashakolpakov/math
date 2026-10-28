import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorMaps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

/-! # Sheaf Tensor Unit -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorUnit

noncomputable section

/-! The tensor product of two structure modules has its explicit
multiplication trivialization, including the formula on section tensors. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing

variable (X : Scheme.{0})

def tensorUnitBilinear : HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) where
  app U := LinearMap.mul Γ(X, U) Γ(X, U)
  naturality {_U _V} h x y := (X.presheaf.map h.op).hom.map_mul x y

def tensorUnitHom : HilbertConstruction.Tensor.ProductSheaf.tensorModule (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) ⟶ HilbertConstruction.Line.Bundles.structureModule X :=
  (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm (tensorUnitBilinear X)

theorem tensorUnitHom_apply (U : X.Opens) (x y : Γ(X, U)) :
    (tensorUnitHom X).app U ((SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).app U x y) =
      x * y := by
  have h := (SheafTensorMaps.tensorBilinear_postcomp (tensorUnitHom X)).trans
    ((HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).apply_symm_apply (tensorUnitBilinear X))
  exact congrArg (fun β : HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) =>
    β.app U x y) h

def tensorUnitInv : HilbertConstruction.Line.Bundles.structureModule X ⟶ HilbertConstruction.Tensor.ProductSheaf.tensorModule (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) :=
  (HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).symm ((SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).app ⊤
    (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤)))

theorem tensorUnitInv_one (U : X.Opens) :
    (tensorUnitInv X).app U (1 : Γ(X, U)) =
      (SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).app U (1 : Γ(X, U)) (1 : Γ(X, U)) := by
  have h := HilbertConstruction.Section.Gluing.moduleSectionHomEquiv_restrict _ (tensorUnitInv X) U
  rw [tensorUnitInv, Equiv.apply_symm_apply] at h
  have hn := (SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).naturality U.leTop
    (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))
  have hu : (HilbertConstruction.Line.Bundles.structureModule X).presheaf.map U.leTop.op (1 : Γ(X, ⊤)) = (1 : Γ(X, U)) :=
    (X.presheaf.map U.leTop.op).hom.map_one
  rw [hu] at hn
  exact h.symm.trans hn

theorem tensorUnitInv_apply (U : X.Opens) (x : Γ(X, U)) :
    (tensorUnitInv X).app U x =
      x • (SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).app U (1 : Γ(X, U)) (1 : Γ(X, U)) := by
  have h := (tensorUnitInv X).app_smul x (1 : Γ(X, U))
  change (tensorUnitInv X).app U (show Γ(X, U) from x * 1) =
    x • (tensorUnitInv X).app U (1 : Γ(X, U)) at h
  simpa only [mul_one, tensorUnitInv_one] using h

theorem tensorUnit_inv_hom : tensorUnitInv X ≫ tensorUnitHom X = 𝟙 _ := by
  apply (HilbertConstruction.Global.Sections.moduleSectionHomEquiv _).injective
  change (tensorUnitHom X).app ⊤ ((tensorUnitInv X).app ⊤ (1 : Γ(X, ⊤))) = (1 : Γ(X, ⊤))
  rw [tensorUnitInv_one, tensorUnitHom_apply, one_mul]

theorem tensorUnit_hom_inv : tensorUnitHom X ≫ tensorUnitInv X = 𝟙 _ := by
  apply (HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).injective
  rw [← SheafTensorMaps.tensorBilinear_postcomp, HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.postcomp_comp,
    SheafTensorMaps.tensorBilinear_postcomp]
  change ((HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _)
    ((HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.tensorHomEquiv _ _ _).symm (tensorUnitBilinear X))).postcomp _ = _
  rw [Equiv.apply_symm_apply]
  apply HilbertConstruction.Bilinear.Sheaves.SheafBilinearMap.ext
  intro U
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change Γ(X, U) at x y
  change (tensorUnitInv X).app U (show Γ(X, U) from x * y) =
    (SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).app U x y
  rw [tensorUnitInv_apply]
  let β : Γ(X, U) →ₗ[Γ(X, U)] Γ(X, U) →ₗ[Γ(X, U)]
      Γ(HilbertConstruction.Tensor.ProductSheaf.tensorModule (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X), U) :=
    (SheafTensorMaps.tensorBilinear (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X)).app U
  change (x * y) • β 1 1 = β x y
  have hx := β.map_smul x (1 : Γ(X, U))
  have hy := (β (1 : Γ(X, U))).map_smul y (1 : Γ(X, U))
  have hxy := congrArg (fun f => f y) hx
  change β (x * 1) y = x • β 1 y at hxy
  change β 1 (y * 1) = y • β 1 1 at hy
  rw [mul_one] at hxy hy
  rw [hxy, hy, mul_smul]

def sheafTensorUnitIso : HilbertConstruction.Tensor.ProductSheaf.tensorModule (HilbertConstruction.Line.Bundles.structureModule X) (HilbertConstruction.Line.Bundles.structureModule X) ≅ HilbertConstruction.Line.Bundles.structureModule X where
  hom := tensorUnitHom X
  inv := tensorUnitInv X
  hom_inv_id := tensorUnit_hom_inv X
  inv_hom_id := tensorUnit_inv_hom X

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.SheafTensorUnit
