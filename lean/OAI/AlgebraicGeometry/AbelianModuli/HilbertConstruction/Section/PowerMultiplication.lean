import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Gluing
import Mathlib.LinearAlgebra.Multilinear.Curry

/-! # Power Multiplication -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-!
Multiplication by a fixed section as an actual morphism between consecutive
tensor-power sheaves. This gives global transition maps for increasing degrees
while reconciling locally constructed extensions.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {L M : X.Modules} {n : ℕ}

/-- Insert the value of a section into the first input of a sheaf multilinear map. -/
def Tensor.Powers.SheafMultilinearMap.insertSection (β : Tensor.Powers.SheafMultilinearMap L (n + 1) M)
    (s : Line.Bundles.structureModule X ⟶ L) : Tensor.Powers.SheafMultilinearMap L n M where
  app U := (β.app U).curryLeft (s.app U (1 : Γ(X, U)))
  naturality {U V} h v := by
    have hs : L.presheaf.map h.op (s.app U (1 : Γ(X, U))) = s.app V (1 : Γ(X, V)) :=
      (L.unitHomEquiv s).property h.op
    have hc : (fun i : Fin (n + 1) =>
        L.presheaf.map h.op
          (Fin.cons (α := fun _ : Fin (n + 1) => Γ(L, U)) (s.app U (1 : Γ(X, U))) v i)) =
        Fin.cons (α := fun _ : Fin (n + 1) => Γ(L, V))
          (s.app V (1 : Γ(X, V))) (fun i => L.presheaf.map h.op (v i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hs
      · rfl
    exact (β.naturality h (Fin.cons (s.app U (1 : Γ(X, U))) v)).trans
      (congrArg (β.app V) hc)

/-- Multiply sections of the nth tensor power by a fixed section of the line bundle. -/
def Section.PowerMultiplication.multiplyPowerBySection (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) :
    TensorPower.PowerSheaf.tensorPowerModule L n ⟶ TensorPower.PowerSheaf.tensorPowerModule L (n + 1) :=
  (TensorPower.PowerSheaf.tensorPowerHomEquiv L (TensorPower.PowerSheaf.tensorPowerModule L (n + 1)) n).symm
    ((TensorPower.Maps.tensorPowerMultilinear L (n + 1)).insertSection s)

theorem Section.PowerMultiplication.multiplyPowerBySection_spec (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) :
    (TensorPower.Maps.tensorPowerMultilinear L n).postcomp (Section.PowerMultiplication.multiplyPowerBySection s n) =
      (TensorPower.Maps.tensorPowerMultilinear L (n + 1)).insertSection s :=
  (TensorPower.Maps.tensorPowerMultilinear_postcomp _).trans
    ((TensorPower.PowerSheaf.tensorPowerHomEquiv L (TensorPower.PowerSheaf.tensorPowerModule L (n + 1)) n).apply_symm_apply _)

/-- Multiplying the nth power of a section by that section gives its next power. -/
theorem Section.PowerMultiplication.tensorPowerSection_multiply (s : Line.Bundles.structureModule X ⟶ L) (n : ℕ) :
    TensorPower.Maps.tensorPowerSection s n ≫ Section.PowerMultiplication.multiplyPowerBySection s n = TensorPower.Maps.tensorPowerSection s (n + 1) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  change (Section.PowerMultiplication.multiplyPowerBySection s n).app U ((TensorPower.Maps.tensorPowerSection s n).app U r) =
    (TensorPower.Maps.tensorPowerSection s (n + 1)).app U r
  rw [TensorPower.Maps.tensorPowerSection_app, TensorPower.Maps.tensorPowerSection_app]
  have he := congrArg (fun β : Tensor.Powers.SheafMultilinearMap L n (TensorPower.PowerSheaf.tensorPowerModule L (n + 1)) =>
    β.app U (fun _ => s.app U (1 : Γ(X, U)))) (Section.PowerMultiplication.multiplyPowerBySection_spec s n)
  have hc : Fin.cons (s.app U (1 : Γ(X, U))) (fun _ : Fin n => s.app U (1 : Γ(X, U))) =
      (fun _ : Fin (n + 1) => s.app U (1 : Γ(X, U))) := by
    funext i
    refine Fin.cases rfl (fun _ => rfl) i
  change (Section.PowerMultiplication.multiplyPowerBySection s n).app U
      ((TensorPower.Maps.tensorPowerMultilinear L n).app U (fun _ => s.app U (1 : Γ(X, U)))) =
    (TensorPower.Maps.tensorPowerMultilinear L (n + 1)).app U
      (Fin.cons (s.app U (1 : Γ(X, U))) (fun _ => s.app U (1 : Γ(X, U)))) at he
  exact ((Section.PowerMultiplication.multiplyPowerBySection s n).app_smul r _).trans
    (congrArg (fun z : Γ(TensorPower.PowerSheaf.tensorPowerModule L (n + 1), U) => r • z)
      (he.trans (congrArg ((TensorPower.Maps.tensorPowerMultilinear L (n + 1)).app U) hc)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
