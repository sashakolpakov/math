import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.Derivation.Basic

/-! # Numbers -/

namespace OAI.RepresentationTheory.Theta.Geometric.Dual.Numbers

noncomputable section

/-! Point derivations are precisely maps to the dual numbers with fixed
reduction. This construction is valid over every field. -/

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]
  [Algebra R k] [IsScalarTower k R k]

def derivationDualNumber (δ : Derivation k R k) : R →ₐ[k] DualNumber k where
  toFun a := (algebraMap R k a, δ a)
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero (algebraMap R k)
    · exact map_zero δ
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one (algebraMap R k)
    · exact δ.map_one_eq_zero
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact map_add (algebraMap R k) a b
    · exact map_add δ a b
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul (algebraMap R k) a b
    · change δ (a * b) = algebraMap R k a * δ b + δ a * algebraMap R k b
      simpa only [Algebra.smul_def, mul_comm] using δ.leibniz a b
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact (IsScalarTower.algebraMap_apply k R k c).symm
    · exact δ.map_algebraMap c

def dualNumberPointDerivation
    (f : {f : R →ₐ[k] DualNumber k // ∀ a, (f a).fst = algebraMap R k a}) :
    Derivation k R k where
  toFun a := (f.val a).snd
  map_add' a b := by rw [map_add, TrivSqZeroExt.snd_add]
  map_smul' c a := by
    rw [map_smul, TrivSqZeroExt.snd_smul]
    rfl
  map_one_eq_zero' := by
    change (f.val 1).snd = 0
    rw [map_one]; rfl
  leibniz' a b := by
    change (f.val (a * b)).snd = a • (f.val b).snd + b • (f.val a).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, f.property a, f.property b]
    simp [Algebra.smul_def, add_comm, mul_comm]

def derivationDualNumberEquiv : Derivation k R k ≃
    {f : R →ₐ[k] DualNumber k // ∀ a, (f a).fst = algebraMap R k a} where
  toFun δ := ⟨derivationDualNumber δ, fun _ => rfl⟩
  invFun := dualNumberPointDerivation
  left_inv δ := by apply Derivation.ext; intro a; rfl
  right_inv f := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    apply TrivSqZeroExt.ext
    · exact (f.property a).symm
    · rfl

end

end OAI.RepresentationTheory.Theta.Geometric.Dual.Numbers
