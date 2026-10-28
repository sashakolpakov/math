import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Maps
import Mathlib.Algebra.Group.Commute.Units
import Mathlib.CategoryTheory.Endomorphism

/-! # Units -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units

noncomputable section

/-! Positive tensor powers detect invertibility of maps between trivialized line bundles. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators

universe u

variable {X : Scheme.{u}}

/-- A structure-module endomorphism acts by multiplication by its value on one. -/
theorem structureModuleEnd_app (a : End (Line.Bundles.structureModule X)) (U : X.Opens) (r : Γ(X, U)) :
    a.app U r = r * (show Γ(X, U) from a.app U (1 : Γ(X, U))) := by
  have ha := a.app_smul r (1 : Γ(X, U))
  change a.app U (r * (1 : Γ(X, U))) = r * (show Γ(X, U) from a.app U (1 : Γ(X, U))) at ha
  exact (congrArg (fun z : Γ(X, U) => a.app U z) (mul_one r)).symm.trans ha

/-- Composition powers of a structure-module endomorphism are ordinary powers of its local function. -/
theorem structureModuleEnd_pow_app (a : End (Line.Bundles.structureModule X)) (n : ℕ) (U : X.Opens)
    (r : Γ(X, U)) :
    (a ^ n).app U r = r * (show Γ(X, U) from a.app U (1 : Γ(X, U))) ^ n := by
  induction n with
  | zero =>
    change r = r * (show Γ(X, U) from a.app U (1 : Γ(X, U))) ^ 0
    rw [pow_zero, mul_one]
  | succ n ih =>
    rw [pow_succ']
    change a.app U ((a ^ n).app U r) = _
    exact (structureModuleEnd_app a U _).trans
      ((congrArg (fun z : Γ(X, U) => z * (show Γ(X, U) from a.app U (1 : Γ(X, U)))) ih).trans
        (by rw [pow_succ, mul_assoc]))

/-- Under the canonical unit comparison, the tensor power of scalar multiplication is its ordinary power. -/
theorem tensorPowerMap_unit_conjugation (a : End (Line.Bundles.structureModule X)) (n : ℕ) :
    (Maps.tensorPowerUnitIso X n).inv ≫ Maps.tensorPowerMap a n ≫ (Maps.tensorPowerUnitIso X n).hom = a ^ n := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro r
  change Γ(X, U) at r
  have he := congrArg (fun β : Tensor.Powers.SheafMultilinearMap (Line.Bundles.structureModule X) n (Line.Bundles.structureModule X) =>
    β.app U (fun _ => a.app U (1 : Γ(X, U)))) (Maps.tensorPowerUnitHom_spec X n)
  change (Maps.tensorPowerUnitHom X n).app U
      ((Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U
        (fun _ => a.app U (1 : Γ(X, U)))) =
    (show Γ(X, U) from ∏ _ : Fin n, (show Γ(X, U) from a.app U (1 : Γ(X, U)))) at he
  change (Maps.tensorPowerUnitHom X n).app U ((Maps.tensorPowerSection a n).app U r) = (a ^ n).app U r
  rw [Maps.tensorPowerSection_app]
  let c : Γ(X, U) := a.app U (1 : Γ(X, U))
  have hp : (∏ _ : Fin n, c) = c ^ n := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hm := (Maps.tensorPowerUnitHom X n).app_smul r
    ((Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => c))
  change (Maps.tensorPowerUnitHom X n).app U
      (r • (Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => c)) =
    r * (show Γ(X, U) from (Maps.tensorPowerUnitHom X n).app U
      ((Maps.tensorPowerMultilinear (Line.Bundles.structureModule X) n).app U (fun _ => c))) at hm
  exact hm.trans ((congrArg (fun z : Γ(X, U) => r * z) (he.trans hp)).trans
    (structureModuleEnd_pow_app a n U r).symm)

/-- Taking a positive tensor power reflects invertibility for structure-module endomorphisms. -/
theorem isIso_of_tensorPowerMap_unit (a : End (Line.Bundles.structureModule X)) (n : ℕ) (hn : 0 < n)
    [IsIso (Maps.tensorPowerMap a n)] : IsIso a := by
  have : IsIso (a ^ n) := (tensorPowerMap_unit_conjugation a n) ▸ inferInstance
  exact (isUnit_iff_isIso a).mp
    ((isUnit_pow_iff (Nat.ne_of_gt hn)).mp ((isUnit_iff_isIso (a ^ n)).mpr this))

/-- A positive tensor power detects invertibility when both sheaves have chosen line-bundle frames. -/
theorem isIso_of_tensorPowerMap_of_frames {L M : X.Modules} (a : L ⟶ M) (n : ℕ) (hn : 0 < n)
    (e : L ≅ Line.Bundles.structureModule X) (h : M ≅ Line.Bundles.structureModule X)
    [IsIso (Maps.tensorPowerMap a n)] : IsIso a := by
  let b : End (Line.Bundles.structureModule X) := e.inv ≫ a ≫ h.hom
  have hb : Maps.tensorPowerMap b n = Maps.tensorPowerMap e.inv n ≫ Maps.tensorPowerMap a n ≫ Maps.tensorPowerMap h.hom n := by
    dsimp [b]
    rw [Maps.tensorPowerMap_comp, Maps.tensorPowerMap_comp]
  have : IsIso (Maps.tensorPowerMap e.inv n) := (Maps.tensorPowerFunctor X n).map_isIso e.inv
  have : IsIso (Maps.tensorPowerMap h.hom n) := (Maps.tensorPowerFunctor X n).map_isIso h.hom
  have : IsIso (Maps.tensorPowerMap b n) := hb.symm ▸ inferInstance
  have : IsIso b := isIso_of_tensorPowerMap_unit b n hn
  have hab : a = e.hom ≫ b ≫ h.inv := by simp [b]
  rw [hab]
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Units
