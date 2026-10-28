import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf

/-! # Tensor Power Sheaf -/

namespace OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerSheaf

noncomputable section

/-!
# Homomorphisms: tensor powers of module sheaves

Sheafification of the pointwise tensor power has the required universal
property for actual sheaf-multilinear maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf

set_option backward.isDefEq.respectTransparency.types false

namespace Construction

universe u

variable {X : Scheme.{u}} (L : X.Modules) (n : ℕ)

def tensorPowerSheaf : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n)

def tensorPowerPresheafToMultilinear (P : X.Modules)
    (f : AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val) : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P where
  app U := by
    let g : PiTensorProduct Γ(X, U) (fun _ : Fin n => Γ(L, U)) →ₗ[Γ(X, U)] Γ(P, U) :=
      (f.app (.op U)).hom
    exact g.compMultilinearMap (PiTensorProduct.tprod Γ(X, U))
  naturality {U V} h s := by
    exact (PresheafOfModules.naturality_apply f h.op (PiTensorProduct.tprod Γ(X, U) s)).symm.trans
      (congrArg (f.app (.op V)) (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod L n h.op s))

def multilinearToTensorPowerPresheaf (P : X.Modules) (β : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P) :
    AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val where
  app U := ModuleCat.ofHom (PiTensorProduct.lift (β.app U.unop))
  naturality {U V} h := by
    let Q : ModuleCat Γ(X, U.unop) :=
      (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (P.val.obj V)
    let : Module Γ(X, U.unop) Q := Q.isModule
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext (R := Γ(X, U.unop)) (E := Q)
    apply MultilinearMap.ext
    intro s
    change PiTensorProduct.lift (β.app V.unop)
        (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction L n h (PiTensorProduct.tprod Γ(X, U.unop) s)) =
      P.val.map h (PiTensorProduct.lift (β.app U.unop) (PiTensorProduct.tprod Γ(X, U.unop) s))
    rw [AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    exact (β.naturality h.unop s).symm

def tensorPowerPresheafHomEquiv (P : X.Modules) :
    (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val) ≃ AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P where
  toFun := tensorPowerPresheafToMultilinear L n P
  invFun := multilinearToTensorPowerPresheaf L n P
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext (R := Γ(X, U.unop))
    apply MultilinearMap.ext
    intro s
    exact PiTensorProduct.lift.tprod (φ := (tensorPowerPresheafToMultilinear L n P f).app U.unop) s
  right_inv β := by
    ext U s
    exact PiTensorProduct.lift.tprod (φ := β.app U) s

def tensorPowerSheafHomEquiv (P : X.Modules) :
    (tensorPowerSheaf L n ⟶ P) ≃ AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n P :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n) P).trans (tensorPowerPresheafHomEquiv L n P)

def tensorPowerSheafMultilinear : AbelianModuli.HilbertConstruction.Tensor.Powers.SheafMultilinearMap L n (tensorPowerSheaf L n) :=
  tensorPowerSheafHomEquiv L n _ (𝟙 _)

theorem tensorPowerSheafMultilinear_postcomp (P : X.Modules) (f : tensorPowerSheaf L n ⟶ P) :
    (tensorPowerSheafMultilinear L n).postcomp f = tensorPowerSheafHomEquiv L n P f := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  have h := adj.homEquiv_naturality_right (𝟙 (tensorPowerSheaf L n)) f
  erw [Category.id_comp] at h
  ext U s
  change f.app U (((adj.homEquiv _ _ (𝟙 (tensorPowerSheaf L n))).app (.op U))
    (PiTensorProduct.tprod Γ(X, U) s)) =
      ((adj.homEquiv _ P f).app (.op U)) (PiTensorProduct.tprod Γ(X, U) s)
  rw [h]
  rfl

theorem tensorPowerSheaf_isTensorPower : AbelianModuli.HilbertConstruction.Tensor.Powers.IsTensorPower L n (tensorPowerSheaf L n) := by
  refine ⟨tensorPowerSheafMultilinear L n, fun P => ?_⟩
  have h : (fun f : tensorPowerSheaf L n ⟶ P => (tensorPowerSheafMultilinear L n).postcomp f) =
      tensorPowerSheafHomEquiv L n P := funext (tensorPowerSheafMultilinear_postcomp L n P)
  rw [h]
  exact (tensorPowerSheafHomEquiv L n P).bijective

end Construction

end

end OAI.AlgebraicGeometry.Picard.Homomorphisms.TensorPowerSheaf
