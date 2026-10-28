import Mathlib.Algebra.DualNumber
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Number Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients

noncomputable section

/-! The two coefficients on an actual scalar-extended affine dual-number
chart, with functoriality under the original algebra maps. -/

open scoped TensorProduct

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]

instance dualNumberScalarTower (K A : Type*) [CommRing K] [CommRing A] [Algebra K A] :
    IsScalarTower K (DualNumber A) (DualNumber A) := by
  constructor
  intro r x y
  apply TrivSqZeroExt.ext
  · change (r • x.fst) * y.fst = r • (x.fst * y.fst)
    simp [Algebra.smul_def, mul_assoc]
  · change (r • x.fst) * y.snd + (r • x.snd) * y.fst =
      r • (x.fst * y.snd + x.snd * y.fst)
    simp [Algebra.smul_def, mul_add, mul_assoc]

instance dualNumberSMulCommClass (K A : Type*) [CommRing K] [CommRing A] [Algebra K A] :
    SMulCommClass K (DualNumber A) (DualNumber A) := by
  constructor
  intro r x y
  apply TrivSqZeroExt.ext
  · change r • (x.fst * y.fst) = x.fst * (r • y.fst)
    simp [Algebra.smul_def, mul_left_comm]
  · change r • (x.fst * y.snd + x.snd * y.fst) =
      x.fst * (r • y.snd) + x.snd * (r • y.fst)
    simp only [Algebra.smul_def]
    ring

def dualNumberRingMap (f : R →+* S) : DualNumber R →+* DualNumber S where
  toFun x := (f x.fst, f x.snd)
  map_zero' := by apply TrivSqZeroExt.ext <;> exact map_zero f
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one f
    · exact map_zero f
  map_add' x y := by apply TrivSqZeroExt.ext <;> exact map_add f _ _
  map_mul' x y := by
    apply TrivSqZeroExt.ext
    · exact map_mul f _ _
    · change f (x.fst * y.snd + x.snd * y.fst) = _
      rw [map_add, map_mul, map_mul]
      rfl

def dualNumberAlgMap [Algebra k R] [Algebra k S] (f : R →ₐ[k] S) :
    DualNumber R →ₐ[k] DualNumber S where
  toRingHom := dualNumberRingMap f.toRingHom
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact f.commutes c
    · exact map_zero f

variable [Algebra k R]

def dualTensorCoefficients (k R : Type*) [CommRing k] [CommRing R] [Algebra k R] :
    (DualNumber k ⊗[k] R) →ₐ[k] DualNumber R :=
  Algebra.TensorProduct.lift (dualNumberAlgMap (Algebra.ofId k R))
    (TrivSqZeroExt.inlAlgHom k R R) (fun _ _ => Commute.all _ _)

theorem dualTensorCoefficients_tmul (c : DualNumber k) (a : R) :
    dualTensorCoefficients k R (c ⊗ₜ[k] a) = (show DualNumber R from (c.fst • a, c.snd • a)) := by
  rw [dualTensorCoefficients, Algebra.TensorProduct.lift_tmul]
  apply TrivSqZeroExt.ext
  · exact (Algebra.smul_def c.fst a).symm
  · change algebraMap k R c.fst * 0 + algebraMap k R c.snd * a = c.snd • a
    rw [mul_zero, zero_add, Algebra.smul_def]

def dualTensorFromCoefficients (k R : Type*) [CommRing k] [CommRing R] [Algebra k R] :
    DualNumber R →ₐ[k] (DualNumber k ⊗[k] R) :=
  DualNumber.lift (R := k) (A := R) (B := DualNumber k ⊗[k] R)
    ⟨((Algebra.TensorProduct.includeRight : R →ₐ[k] DualNumber k ⊗[k] R),
    (Algebra.TensorProduct.includeLeft : DualNumber k →ₐ[k] DualNumber k ⊗[k] R) DualNumber.eps),
    (by rw [← map_mul, DualNumber.eps_mul_eps, map_zero]), fun a => by
      exact Commute.all
        ((Algebra.TensorProduct.includeLeft : DualNumber k →ₐ[k] DualNumber k ⊗[k] R) DualNumber.eps)
        ((Algebra.TensorProduct.includeRight : R →ₐ[k] DualNumber k ⊗[k] R) a)⟩

theorem dualTensorFromCoefficients_apply (a : DualNumber R) :
    dualTensorFromCoefficients k R a = (1 : DualNumber k) ⊗ₜ[k] a.fst +
      (DualNumber.eps : DualNumber k) ⊗ₜ[k] a.snd := by
  rw [dualTensorFromCoefficients, DualNumber.lift_apply_apply]
  change (1 : DualNumber k) ⊗ₜ[k] a.fst +
    ((1 : DualNumber k) ⊗ₜ[k] a.snd) * ((DualNumber.eps : DualNumber k) ⊗ₜ[k] 1) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

theorem dualTensorCoefficients_rightInverse (a : DualNumber R) :
    dualTensorCoefficients k R (dualTensorFromCoefficients k R a) = a := by
  rw [dualTensorFromCoefficients_apply, map_add, dualTensorCoefficients_tmul,
    dualTensorCoefficients_tmul]
  apply TrivSqZeroExt.ext
  · change (1 : k) • a.fst + (0 : k) • a.snd = a.fst
    rw [one_smul, zero_smul, add_zero]
  · change (0 : k) • a.fst + (1 : k) • a.snd = a.snd
    rw [zero_smul, one_smul, zero_add]

theorem dualTensorCoefficients_leftInverse (u : DualNumber k ⊗[k] R) :
    dualTensorFromCoefficients k R (dualTensorCoefficients k R u) = u := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, map_add, hu, hv]
  | tmul c a =>
    rw [dualTensorCoefficients_tmul, dualTensorFromCoefficients_apply]
    change (1 : DualNumber k) ⊗ₜ[k] (c.fst • a) +
      (DualNumber.eps : DualNumber k) ⊗ₜ[k] (c.snd • a) = c ⊗ₜ[k] a
    rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul]
    congr 1
    apply TrivSqZeroExt.ext <;> simp

def dualTensorCoefficientEquiv (k R : Type*) [CommRing k] [CommRing R] [Algebra k R] :
    (DualNumber k ⊗[k] R) ≃ₐ[k] DualNumber R :=
  AlgEquiv.ofAlgHom (dualTensorCoefficients k R) (dualTensorFromCoefficients k R)
    (AlgHom.ext dualTensorCoefficients_rightInverse) (AlgHom.ext dualTensorCoefficients_leftInverse)

theorem dualTensorCoefficients_natural [Algebra k S] (f : R →ₐ[k] S)
    (u : DualNumber k ⊗[k] R) :
    dualTensorCoefficients k S (Algebra.TensorProduct.map (AlgHom.id k (DualNumber k)) f u) =
      dualNumberAlgMap f (dualTensorCoefficients k R u) := by
  induction u using TensorProduct.inductionOn with
  | add u v hu hv => rw [map_add, map_add, map_add, map_add, hu, hv]
  | tmul c a =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, dualTensorCoefficients_tmul,
      dualTensorCoefficients_tmul]
    apply TrivSqZeroExt.ext <;> exact (map_smul f _ _).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.NumberCoefficients
