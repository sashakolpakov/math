import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.Powers
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-! # Presheaf -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf

noncomputable section

/-! The presheaf tensor power, with restriction maps over the varying coordinate rings. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {X : Scheme.{u}}

/-- Tensor-power sections before sheafification. -/
def tensorPowerSections (L : X.Modules) (n : ℕ) (U : X.Opens) : ModuleCat Γ(X, U) :=
  ModuleCat.of Γ(X, U) (PiTensorProduct Γ(X, U) (fun _ : Fin n => Γ(L, U)))

/-- Restrict every entry of a tensor-generating tuple. -/
def tensorPowerVectorMap (L : X.Modules) {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    {n : ℕ} (s : Fin n → Γ(L, U.unop)) : Fin n → Γ(L, V.unop) :=
  fun i => L.val.map h (s i)

theorem tensorPowerVectorMap_update (L : X.Modules) {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    {n : ℕ} [DecidableEq (Fin n)] (s : Fin n → Γ(L, U.unop)) (i : Fin n) (x : Γ(L, U.unop)) :
    tensorPowerVectorMap L h (Function.update s i x) =
      Function.update (tensorPowerVectorMap L h s) i (L.val.map h x) :=
  Function.comp_update (fun x => L.val.map h x) s i x

/-- Restriction of tensor generators is multilinear over the original coordinate ring. -/
def tensorPowerRestrictionMultilinear (L : X.Modules) (n : ℕ)
    {U V : X.Opensᵒᵖ} (h : U ⟶ V) :
    MultilinearMap Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop))
      ((ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop)) where
  toFun s := PiTensorProduct.tprod Γ(X, V.unop) (tensorPowerVectorMap L h s)
  map_update_add' s i x y := by
    let t := PiTensorProduct.tprod Γ(X, V.unop) (s := fun _ : Fin n => Γ(L, V.unop))
    exact (congrArg t (tensorPowerVectorMap_update L h s i (x + y))).trans
      ((congrArg (fun a => t (Function.update (tensorPowerVectorMap L h s) i a))
        ((L.val.map h).hom.map_add x y)).trans
        ((t.map_update_add (tensorPowerVectorMap L h s) i _ _).trans
          (congrArg₂ (fun a b => t a + t b)
            (tensorPowerVectorMap_update L h s i x).symm
            (tensorPowerVectorMap_update L h s i y).symm)))
  map_update_smul' s i r x := by
    let t := PiTensorProduct.tprod Γ(X, V.unop) (s := fun _ : Fin n => Γ(L, V.unop))
    exact (congrArg t (tensorPowerVectorMap_update L h s i (r • x))).trans
      ((congrArg (fun a => t (Function.update (tensorPowerVectorMap L h s) i a))
        (L.val.map_smul h r x)).trans
        ((t.map_update_smul (tensorPowerVectorMap L h s) i (X.presheaf.map h r) _).trans
          (congrArg (fun a => (X.presheaf.map h r) • t a)
            (tensorPowerVectorMap_update L h s i x).symm)))

/-- The linear restriction map on tensor-power sections. -/
def tensorPowerRestriction (L : X.Modules) (n : ℕ) {U V : X.Opensᵒᵖ} (h : U ⟶ V) :
    tensorPowerSections L n U.unop ⟶
      (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop) := by
  let Q : ModuleCat Γ(X, U.unop) :=
    (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop)
  let : Module Γ(X, U.unop) Q := Q.isModule
  exact (ModuleCat.ofHom (Y := Q)
    (PiTensorProduct.lift (E := Q) (tensorPowerRestrictionMultilinear L n h)) :
    ModuleCat.of Γ(X, U.unop) (PiTensorProduct Γ(X, U.unop) (fun _ : Fin n => Γ(L, U.unop))) ⟶ Q)

@[simp]
theorem tensorPowerRestriction_tprod (L : X.Modules) (n : ℕ) {U V : X.Opensᵒᵖ} (h : U ⟶ V)
    (s : Fin n → Γ(L, U.unop)) :
    tensorPowerRestriction L n h (PiTensorProduct.tprod Γ(X, U.unop) s) =
      PiTensorProduct.tprod Γ(X, V.unop) (tensorPowerVectorMap L h s) := by
  let Q : ModuleCat Γ(X, U.unop) :=
    (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj (tensorPowerSections L n V.unop)
  let : Module Γ(X, U.unop) Q := Q.isModule
  exact PiTensorProduct.lift.tprod (φ := tensorPowerRestrictionMultilinear L n h) s

/-- The presheaf of tensor powers of a module sheaf. -/
def tensorPowerPresheaf (L : X.Modules) (n : ℕ) : X.PresheafOfModules where
  obj U := tensorPowerSections L n U.unop
  map h := tensorPowerRestriction L n h
  map_id U := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro s
    exact (tensorPowerRestriction_tprod L n (𝟙 U) s).trans
      (congrArg (PiTensorProduct.tprod Γ(X, U.unop))
        (funext (fun i => ConcreteCategory.congr_hom (L.val.map_id U) (s i))))
  map_comp f h := by
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro s
    change tensorPowerRestriction L n (f ≫ h) (PiTensorProduct.tprod _ s) =
      tensorPowerRestriction L n h (tensorPowerRestriction L n f (PiTensorProduct.tprod _ s))
    rw [tensorPowerRestriction_tprod, tensorPowerRestriction_tprod, tensorPowerRestriction_tprod]
    congr 1
    funext i
    exact L.val.map_comp_apply f h (s i)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Presheaf
