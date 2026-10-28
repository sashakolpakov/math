import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Multilinear Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Composition of sheaf-multilinear maps and the resulting map between iterated tensor powers. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M P Q : X.Modules} {n m : ℕ}

/-- Flatten the indices of m groups of n tensor factors. -/
def MultilinearComposition.tensorPowerIndexEquiv (m n : ℕ) : (Σ _ : Fin m, Fin n) ≃ Fin (m * n) :=
  (Equiv.sigmaEquivProd (Fin m) (Fin n)).trans finProdFinEquiv

section

/-- Substitute an n-multilinear sheaf map into each argument of an m-multilinear sheaf map. -/
def Tensor.Powers.SheafMultilinearMap.compose (γ : Tensor.Powers.SheafMultilinearMap M m P) (β : Tensor.Powers.SheafMultilinearMap L n M) :
    Tensor.Powers.SheafMultilinearMap L (m * n) P where
  app U := ((γ.app U).compMultilinearMap (fun _ : Fin m => β.app U)).domDomCongr
    (MultilinearComposition.tensorPowerIndexEquiv m n)
  naturality {U V} h s :=
    (γ.naturality h (fun i => β.app U (fun j => s (MultilinearComposition.tensorPowerIndexEquiv m n ⟨i, j⟩)))).trans
      (congrArg (γ.app V) (funext fun i =>
        β.naturality h (fun j => s (MultilinearComposition.tensorPowerIndexEquiv m n ⟨i, j⟩))))

theorem Tensor.Powers.SheafMultilinearMap.compose_postcomp (γ : Tensor.Powers.SheafMultilinearMap M m P) (β : Tensor.Powers.SheafMultilinearMap L n M)
    (a : P ⟶ Q) : (γ.compose β).postcomp a = (γ.postcomp a).compose β := by
  ext U s
  rfl

theorem Tensor.Powers.SheafMultilinearMap.compose_precomp (γ : Tensor.Powers.SheafMultilinearMap M m P) (β : Tensor.Powers.SheafMultilinearMap L n M)
    (a : Q ⟶ L) : (γ.compose β).precomp a = γ.compose (β.precomp a) := by
  ext U s
  rfl

theorem Tensor.Powers.SheafMultilinearMap.compose_middle (γ : Tensor.Powers.SheafMultilinearMap M m P) (β : Tensor.Powers.SheafMultilinearMap L n Q)
    (a : Q ⟶ M) : (γ.precomp a).compose β = γ.compose (β.postcomp a) := by
  ext U s
  rfl

end

/-- The universal map from a single power to the corresponding iterated tensor power. -/
def MultilinearComposition.tensorPowerComposeMap (L : X.Modules) (m n : ℕ) :
    TensorPower.PowerSheaf.tensorPowerModule L (m * n) ⟶ TensorPower.PowerSheaf.tensorPowerModule (TensorPower.PowerSheaf.tensorPowerModule L n) m :=
  (TensorPower.PowerSheaf.tensorPowerHomEquiv L (TensorPower.PowerSheaf.tensorPowerModule (TensorPower.PowerSheaf.tensorPowerModule L n) m) (m * n)).symm
    ((TensorPower.Maps.tensorPowerMultilinear (TensorPower.PowerSheaf.tensorPowerModule L n) m).compose (TensorPower.Maps.tensorPowerMultilinear L n))

theorem MultilinearComposition.tensorPowerComposeMap_spec (L : X.Modules) (m n : ℕ) :
    (TensorPower.Maps.tensorPowerMultilinear L (m * n)).postcomp (MultilinearComposition.tensorPowerComposeMap L m n) =
      (TensorPower.Maps.tensorPowerMultilinear (TensorPower.PowerSheaf.tensorPowerModule L n) m).compose (TensorPower.Maps.tensorPowerMultilinear L n) :=
  (TensorPower.Maps.tensorPowerMultilinear_postcomp _).trans
    ((TensorPower.PowerSheaf.tensorPowerHomEquiv L (TensorPower.PowerSheaf.tensorPowerModule (TensorPower.PowerSheaf.tensorPowerModule L n) m) (m * n)).apply_symm_apply _)

/-- The comparison of single and iterated powers commutes with maps of module sheaves. -/
theorem MultilinearComposition.tensorPowerComposeMap_naturality (a : L ⟶ M) (m n : ℕ) :
    TensorPower.Maps.tensorPowerMap a (m * n) ≫ MultilinearComposition.tensorPowerComposeMap M m n =
      MultilinearComposition.tensorPowerComposeMap L m n ≫ TensorPower.Maps.tensorPowerMap (TensorPower.Maps.tensorPowerMap a n) m := by
  apply TensorPower.Maps.tensorPower_hom_ext
  rw [Tensor.Powers.SheafMultilinearMap.postcomp_comp, TensorPower.Maps.tensorPowerMap_spec,
    ← Tensor.Powers.SheafMultilinearMap.precomp_postcomp, MultilinearComposition.tensorPowerComposeMap_spec,
    Tensor.Powers.SheafMultilinearMap.compose_precomp,
    Tensor.Powers.SheafMultilinearMap.postcomp_comp, MultilinearComposition.tensorPowerComposeMap_spec,
    Tensor.Powers.SheafMultilinearMap.compose_postcomp, TensorPower.Maps.tensorPowerMap_spec,
    Tensor.Powers.SheafMultilinearMap.compose_middle, TensorPower.Maps.tensorPowerMap_spec]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
