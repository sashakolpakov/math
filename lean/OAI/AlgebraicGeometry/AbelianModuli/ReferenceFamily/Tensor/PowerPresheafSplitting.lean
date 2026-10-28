import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerSplitting

/-! # Power Presheaf Splitting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerPresheafSplitting

noncomputable section

/-! The finite tensor splitting commutes with the actual presheaf
restriction maps, including the change of coordinate ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u
variable {X : Scheme.{u}}

def tensorPowerSuccPresheafIso (L : X.Modules) (n : ℕ) :
    HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L (n + 1) ≅
      PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) (HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n) L.val := by
  refine PresheafOfModules.isoMk (fun U => (PowerSplitting.tensorFinSuccSplit Γ(X, U.unop) Γ(L, U.unop) n).toModuleIso) ?_
  intro U V h
  let Q : ModuleCat Γ(X, U.unop) :=
    (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj
      ((PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) (HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n) L.val).obj V)
  let : Module Γ(X, U.unop) Q := Q.isModule
  apply ModuleCat.hom_ext
  apply PiTensorProduct.ext (R := Γ(X, U.unop)) (s := fun _ : Fin (n + 1) => Γ(L, U.unop)) (E := Q)
  apply MultilinearMap.ext
  intro s
  change PowerSplitting.tensorFinSuccSplit Γ(X, V.unop) Γ(L, V.unop) n
      (HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction L (n + 1) h (PiTensorProduct.tprod Γ(X, U.unop) s)) =
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) (HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n) L.val).map h
      (PowerSplitting.tensorFinSuccSplit Γ(X, U.unop) Γ(L, U.unop) n (PiTensorProduct.tprod Γ(X, U.unop) s))
  rw [HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod, PowerSplitting.tensorFinSuccSplit_tprod, PowerSplitting.tensorFinSuccSplit_tprod]
  have ht := PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul (R := X.presheaf)
    (M₁ := HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n) (M₂ := L.val) h
    (PiTensorProduct.tprod Γ(X, U.unop) (fun i : Fin n => s i.castSucc)) (s (Fin.last n))
  refine Eq.trans ?_ ht.symm
  exact (congrArg (fun a : PiTensorProduct Γ(X, V.unop) (fun _ : Fin n => Γ(L, V.unop)) =>
    a ⊗ₜ[Γ(X, V.unop)] (show Γ(L, V.unop) from L.val.map h (s (Fin.last n))))
      (HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod L n h (fun i : Fin n => s i.castSucc))).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.PowerPresheafSplitting
