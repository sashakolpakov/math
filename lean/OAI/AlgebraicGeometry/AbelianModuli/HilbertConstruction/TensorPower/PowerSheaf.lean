import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Power Sheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Existence of sheaf tensor powers with the actual multilinear universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L P Q : X.Modules} {n : ℕ}

section

/-- A morphism from the tensor presheaf gives a natural multilinear map on sections. -/
def Tensor.Powers.SheafMultilinearMap.ofTensorPowerPresheafHom (f : TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val) : Tensor.Powers.SheafMultilinearMap L n P where
  app U := (show PiTensorProduct Γ(X, U) (fun _ : Fin n => Γ(L, U)) →ₗ[Γ(X, U)] Γ(P, U)
    from (f.app (.op U)).hom).compMultilinearMap (PiTensorProduct.tprod Γ(X, U))
  naturality {U V} h s :=
    (PresheafOfModules.naturality_apply f h.op (PiTensorProduct.tprod Γ(X, U) s)).symm.trans
      (congrArg (fun a => f.app (.op V) a) (TensorPower.Presheaf.tensorPowerRestriction_tprod L n h.op s))

/-- A natural multilinear section map extends uniquely to the tensor presheaf. -/
def Tensor.Powers.SheafMultilinearMap.toTensorPowerPresheafHom (β : Tensor.Powers.SheafMultilinearMap L n P) : TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val where
  app U := (ModuleCat.ofHom (PiTensorProduct.lift (β.app U.unop)) :
    ModuleCat.of Γ(X, U.unop) (PiTensorProduct Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop))) ⟶
      ModuleCat.of Γ(X, U.unop) Γ(P, U.unop))
  naturality {U V} h := by
    let Qr : ModuleCat Γ(X, U.unop) :=
      (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (ModuleCat.of Γ(X, V.unop) Γ(P, V.unop))
    let : Module Γ(X, U.unop) Qr := Qr.isModule
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext (R := Γ(X, U.unop)) (s := fun _ : Fin n => Γ(L, U.unop)) (E := Qr)
    apply MultilinearMap.ext
    intro s
    exact (congrArg (PiTensorProduct.lift (β.app V.unop))
      (TensorPower.Presheaf.tensorPowerRestriction_tprod L n h s)).trans
      ((PiTensorProduct.lift.tprod (φ := β.app V.unop) (TensorPower.Presheaf.tensorPowerVectorMap L h s)).trans
        ((β.naturality h.unop s).symm.trans
          (congrArg (fun a => P.presheaf.map h a) (PiTensorProduct.lift.tprod (φ := β.app U.unop) s).symm)))

/-- Universal maps out of the tensor presheaf are exactly natural multilinear maps. -/
def Tensor.Powers.SheafMultilinearMap.tensorPowerPresheafHomEquiv (L P : X.Modules) (n : ℕ) :
    (TensorPower.Presheaf.tensorPowerPresheaf L n ⟶ P.val) ≃ Tensor.Powers.SheafMultilinearMap L n P where
  toFun := Tensor.Powers.SheafMultilinearMap.ofTensorPowerPresheafHom
  invFun := Tensor.Powers.SheafMultilinearMap.toTensorPowerPresheafHom
  left_inv f := by
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    exact PiTensorProduct.lift.apply_symm_apply
      (show PiTensorProduct Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop)) →ₗ[Γ(X, U.unop)]
        Γ(P, U.unop) from (f.app U).hom)
  right_inv β := by
    apply Tensor.Powers.SheafMultilinearMap.ext
    intro U
    exact PiTensorProduct.lift.symm_apply_apply (β.app U)

end

/-- The tensor power of a sheaf of modules, obtained by sheafifying the tensor presheaf. -/
def TensorPower.PowerSheaf.tensorPowerModule (L : X.Modules) (n : ℕ) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (TensorPower.Presheaf.tensorPowerPresheaf L n)

/-- The tensor-power sheaf has the multilinear universal property. -/
def TensorPower.PowerSheaf.tensorPowerHomEquiv (L P : X.Modules) (n : ℕ) :
    (TensorPower.PowerSheaf.tensorPowerModule L n ⟶ P) ≃ Tensor.Powers.SheafMultilinearMap L n P :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (TensorPower.Presheaf.tensorPowerPresheaf L n) P).trans (Tensor.Powers.SheafMultilinearMap.tensorPowerPresheafHomEquiv L P n)

/-- The universal correspondence commutes with postcomposition. -/
theorem TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp (f : TensorPower.PowerSheaf.tensorPowerModule L n ⟶ P) (h : P ⟶ Q) :
    TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n (f ≫ h) = (TensorPower.PowerSheaf.tensorPowerHomEquiv L P n f).postcomp h := by
  have he := (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_naturality_right f h
  change Tensor.Powers.SheafMultilinearMap.ofTensorPowerPresheafHom
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
      (TensorPower.Presheaf.tensorPowerPresheaf L n) Q (f ≫ h)) = _
  rw [he]
  ext U s
  rfl

/-- Every module sheaf has an actual tensor power of every natural degree. -/
theorem TensorPower.PowerSheaf.tensorPowerModule_isTensorPower (L : X.Modules) (n : ℕ) :
    Tensor.Powers.IsTensorPower L n (TensorPower.PowerSheaf.tensorPowerModule L n) := by
  let β := TensorPower.PowerSheaf.tensorPowerHomEquiv L (TensorPower.PowerSheaf.tensorPowerModule L n) n (𝟙 _)
  refine ⟨β, fun Q => ?_⟩
  have he (f : TensorPower.PowerSheaf.tensorPowerModule L n ⟶ Q) : β.postcomp f = TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n f :=
    (TensorPower.PowerSheaf.tensorPowerHomEquiv_postcomp (𝟙 _) f).symm.trans
      (congrArg (TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n) (Category.id_comp f))
  exact ⟨fun f g h => (TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n).injective
    ((he f).symm.trans (h.trans (he g))), fun γ =>
      ⟨(TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n).symm γ,
        (he _).trans ((TensorPower.PowerSheaf.tensorPowerHomEquiv L Q n).apply_symm_apply γ)⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
