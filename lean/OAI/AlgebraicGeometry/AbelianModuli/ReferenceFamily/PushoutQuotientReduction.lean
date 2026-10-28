import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Pushout Quotient Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PushoutQuotientReduction

noncomputable section

section

/-! Base change along a surjective coefficient map identifies the
actual fiber with the quotient by the extended base kernel. The quotient
comparison retains the original algebra map to that fiber. -/

open scoped TensorProduct

def coefficientQuotientReductionEquiv (D k : Type) [CommRing D] [CommRing k] [Algebra D k]
    (h : Function.Surjective (algebraMap D k)) :
    (D ⧸ RingHom.ker (algebraMap D k)) ≃ₐ[D] k :=
  Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId D k) h

variable (D k P B : Type) [CommRing D] [CommRing k] [CommRing P] [CommRing B]
    [Algebra D k] [Algebra D P] [Algebra D B] [Algebra k B] [Algebra P B]
    [IsScalarTower D k B] [IsScalarTower D P B] [Algebra.IsPushout D k P B]
    (h : Function.Surjective (algebraMap D k))

def pushoutQuotientReductionEquiv :
    (P ⧸ (RingHom.ker (algebraMap D k)).map (algebraMap D P)) ≃ₐ[D] B :=
  ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor P (RingHom.ker (algebraMap D k))).restrictScalars D).trans
    ((Algebra.TensorProduct.congr
      (coefficientQuotientReductionEquiv D k h) (AlgEquiv.refl : P ≃ₐ[D] P)).trans
      ((Algebra.IsPushout.equiv D k P B).restrictScalars D))

theorem pushoutQuotientReductionEquiv_mk (p : P) :
    pushoutQuotientReductionEquiv D k P B h
      (Ideal.Quotient.mk ((RingHom.ker (algebraMap D k)).map (algebraMap D P)) p) = algebraMap P B p := by
  change (Algebra.IsPushout.equiv D k P B)
    ((Algebra.TensorProduct.congr
      (coefficientQuotientReductionEquiv D k h) (AlgEquiv.refl : P ≃ₐ[D] P))
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor P (RingHom.ker (algebraMap D k)))
        (Ideal.Quotient.mk ((RingHom.ker (algebraMap D k)).map (algebraMap D P)) p))) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
    Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  simp only [map_one, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_refl, id_eq]
  rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]

include h in
theorem pushoutReduction_surjective : Function.Surjective (algebraMap P B) := by
  intro b
  obtain ⟨q, hq⟩ := (pushoutQuotientReductionEquiv D k P B h).surjective b
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact ⟨p, (pushoutQuotientReductionEquiv_mk D k P B h p).symm.trans hq⟩

include h in
theorem pushoutReduction_kernel :
    RingHom.ker (algebraMap P B) = (RingHom.ker (algebraMap D k)).map (algebraMap D P) := by
  ext p
  change algebraMap P B p = 0 ↔ p ∈ (RingHom.ker (algebraMap D k)).map (algebraMap D P)
  constructor
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply (pushoutQuotientReductionEquiv D k P B h).injective
    rw [pushoutQuotientReductionEquiv_mk, map_zero]
    exact hp
  · intro hp
    rw [← pushoutQuotientReductionEquiv_mk D k P B h p]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

end

/-! The fixed fiber of a scalar-extended affine family is the actual
base change along the coefficient reduction, hence its canonical quotient. -/

variable (R D k S P B : Type) [CommRing R] [CommRing D] [CommRing k]
    [CommRing S] [CommRing P] [CommRing B]
    [Algebra R D] [Algebra R k] [Algebra D k] [IsScalarTower R D k]
    [Algebra R S] [Algebra R P] [Algebra D P] [Algebra S P]
    [IsScalarTower R D P] [IsScalarTower R S P]
    [Algebra R B] [Algebra D B] [Algebra k B] [Algebra S B] [Algebra P B]
    [IsScalarTower R k B] [IsScalarTower D k B] [IsScalarTower D P B]
    [IsScalarTower R S B] [IsScalarTower R P B] [IsScalarTower S P B]
    [hleft : Algebra.IsPushout R D S P] [hfull : Algebra.IsPushout R k S B]

include hleft hfull in
theorem scalarExtensionFiber_isPushout : Algebra.IsPushout D k P B :=
  (Algebra.IsPushout.comp_iff (R := R) (S := D) (R' := S) (S' := P) (T := k) (T' := B)).mp hfull

def scalarExtensionFiberQuotientEquiv (h : Function.Surjective (algebraMap D k)) :
    (P ⧸ (RingHom.ker (algebraMap D k)).map (algebraMap D P)) ≃ₐ[D] B := by
  let : Algebra.IsPushout D k P B := scalarExtensionFiber_isPushout R D k S P B
  exact pushoutQuotientReductionEquiv D k P B h

theorem scalarExtensionFiberQuotientEquiv_mk
    (h : Function.Surjective (algebraMap D k)) (p : P) :
    scalarExtensionFiberQuotientEquiv R D k S P B h
      (Ideal.Quotient.mk ((RingHom.ker (algebraMap D k)).map (algebraMap D P)) p) = algebraMap P B p := by
  let : Algebra.IsPushout D k P B := scalarExtensionFiber_isPushout R D k S P B
  exact pushoutQuotientReductionEquiv_mk D k P B h p

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PushoutQuotientReduction
