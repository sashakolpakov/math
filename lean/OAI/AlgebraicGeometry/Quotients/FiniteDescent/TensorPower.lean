import OAI.AlgebraicGeometry.Quotients.FiniteDescent.BinaryTensorConstructionAssociativity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Tensor Power -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPower.Construction.TensorPowerAddition

noncomputable section

/-! Splitting a tensor power into two blocks gives the binary tensor of the powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite _root_.CategoryTheory.MonoidalCategory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Powers
open scoped TensorProduct

universe u

variable {X : Scheme.{u}}

local instance : MonoidalCategory X.PresheafOfModules :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)

def sectionsIso (L : X.Modules) (m n : ℕ) (U : X.Opens) :
    PiTensorProduct Γ(X, U) (fun _ : Fin (m + n) => Γ(L, U)) ≃ₗ[Γ(X, U)]
      (PiTensorProduct Γ(X, U) (fun _ : Fin m => Γ(L, U))) ⊗[Γ(X, U)]
        (PiTensorProduct Γ(X, U) (fun _ : Fin n => Γ(L, U))) :=
  (PiTensorProduct.reindex Γ(X, U) (fun _ : Fin (m + n) => Γ(L, U))
    finSumFinEquiv.symm).trans (PiTensorProduct.tmulEquiv Γ(X, U) Γ(L, U)).symm

theorem sectionsIso_tprod (L : X.Modules) (m n : ℕ) (U : X.Opens)
    (s : Fin (m + n) → Γ(L, U)) :
    sectionsIso L m n U (PiTensorProduct.tprod Γ(X, U) s) =
      PiTensorProduct.tprod Γ(X, U) (fun i => s (Fin.castAdd n i)) ⊗ₜ
        PiTensorProduct.tprod Γ(X, U) (fun i => s (Fin.natAdd m i)) := by
  simp only [sectionsIso, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod,
    PiTensorProduct.tmulEquiv_symm_apply, Equiv.symm_symm,
    finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

/-- The pointwise block decomposition commutes with restriction of sections. -/
def presheafIso (L : X.Modules) (m n : ℕ) :
    AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L (m + n) ≅ AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L m ⊗ AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n :=
  PresheafOfModules.isoMk (fun U => (sectionsIso L m n U.unop).toModuleIso) (by
    intro U V h
    let T : ModuleCat Γ(X, U.unop) :=
      (ModuleCat.restrictScalars (X.presheaf.map h).hom).obj
        ((AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L m ⊗ AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n).obj V)
    let : Module Γ(X, U.unop) T := T.isModule
    apply ModuleCat.hom_ext
    apply PiTensorProduct.ext (R := Γ(X, U.unop))
      (s := fun _ : Fin (m + n) => Γ(L, U.unop)) (E := T)
    apply MultilinearMap.ext
    intro s
    change sectionsIso L m n V.unop
      (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction L (m + n) h (PiTensorProduct.tprod Γ(X, U.unop) s)) =
      (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L m ⊗ AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n).map h
        (sectionsIso L m n U.unop (PiTensorProduct.tprod Γ(X, U.unop) s))
    rw [AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod, sectionsIso_tprod, sectionsIso_tprod]
    erw [PresheafOfModulesOfCommRing.Monoidal.tensorObj_map_tmul]
    change _ = AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction L m h
      (PiTensorProduct.tprod Γ(X, U.unop) (fun i => s (Fin.castAdd n i))) ⊗ₜ[Γ(X, V.unop)]
        AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction L n h
          (PiTensorProduct.tprod Γ(X, U.unop) (fun i => s (Fin.natAdd m i)))
    rw [AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod, AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerRestriction_tprod]
    rfl)

/-- The block decomposition survives sheafification. -/
def iso (L : X.Modules) (m n : ℕ) :
    AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L (m + n) ≅ AbelianModuli.HilbertConstruction.Tensor.ProductSheaf.tensorModule (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L m) (AbelianModuli.HilbertConstruction.TensorPower.PowerSheaf.tensorPowerModule L n) :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (presheafIso L m n) ≪≫
    (SheafCohomology.Projective.PullbackTensorMonoidal.PresheafOfModules.nonempty_sheafify_tensor_idem X.presheaf X.ringCatSheaf.property
      (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L m) (AbelianModuli.HilbertConstruction.TensorPower.Presheaf.tensorPowerPresheaf L n)).some

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.TensorPower.Construction.TensorPowerAddition
