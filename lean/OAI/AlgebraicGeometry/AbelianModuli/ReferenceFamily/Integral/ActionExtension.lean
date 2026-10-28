import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Action Extension -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionExtension

noncomputable section

/-! Extend an integral number-field action to a rational algebra by
the actual scalar-extension presentation Q tensor O_E = E. The target
algebra may be noncommutative, as for endomorphism rings. -/

open scoped TensorProduct

variable {E D : Type*} [Field E] [NumberField E] [Algebra ℚ E]
  [Ring D] [Algebra ℚ D]

def integralRationalTensorIso : ℚ ⊗[ℤ] NumberField.RingOfIntegers E ≃ₐ[ℚ] E :=
  Algebra.IsPushout.equiv ℤ ℚ (NumberField.RingOfIntegers E) E

def integralActionTensorMap (ρ : NumberField.RingOfIntegers E →+* D) :
    ℚ ⊗[ℤ] NumberField.RingOfIntegers E →ₐ[ℚ] D :=
  Algebra.TensorProduct.lift (Algebra.ofId ℚ D) ρ.toIntAlgHom
    (fun r x => Algebra.commutes r (ρ x))

/-- The extension is a genuine Q-algebra homomorphism into the actual
endomorphism algebra; scalar commutation is built into the tensor map. -/
def extendIntegralAction (ρ : NumberField.RingOfIntegers E →+* D) : E →ₐ[ℚ] D :=
  (integralActionTensorMap ρ).comp integralRationalTensorIso.symm.toAlgHom

theorem extendIntegralAction_tmul (ρ : NumberField.RingOfIntegers E →+* D)
    (q : ℚ) (a : NumberField.RingOfIntegers E) :
    extendIntegralAction ρ (integralRationalTensorIso (q ⊗ₜ[ℤ] a)) = algebraMap ℚ D q * ρ a := by
  change integralActionTensorMap ρ (integralRationalTensorIso.symm
    (integralRationalTensorIso (q ⊗ₜ[ℤ] a))) = _
  rw [AlgEquiv.symm_apply_apply]
  rfl

/-- Commuting with every integral operator implies commuting with the
entire field action, by the explicit rational tensor presentation. -/
theorem extendIntegralAction_commute (ρ : NumberField.RingOfIntegers E →+* D) (z : D)
    (h : ∀ a, Commute (ρ a) z) (x : E) : Commute (extendIntegralAction ρ x) z := by
  obtain ⟨t, rfl⟩ := (integralRationalTensorIso (E := E)).surjective x
  induction t using TensorProduct.inductionOn with
  | add t u ht hu =>
      rw [map_add, map_add]
      exact ht.add_left hu
  | tmul q a =>
      rw [extendIntegralAction_tmul]
      exact (show Commute (algebraMap ℚ D q) z from Algebra.commutes q z).mul_left (h a)

theorem extendIntegralAction_integer (ρ : NumberField.RingOfIntegers E →+* D)
    (a : NumberField.RingOfIntegers E) : extendIntegralAction ρ (a : E) = ρ a := by
  have ha : integralRationalTensorIso (1 ⊗ₜ[ℤ] a) = (a : E) := by
    exact (Algebra.IsPushout.equiv_tmul ℤ ℚ (NumberField.RingOfIntegers E) E 1 a).trans
      ((congrArg (fun x => x * (a : E)) (map_one (algebraMap ℚ E))).trans (one_mul _))
  change integralActionTensorMap ρ (integralRationalTensorIso.symm (a : E)) = ρ a
  rw [← ha, AlgEquiv.symm_apply_apply]
  change (Algebra.ofId ℚ D) 1 * ρ a = ρ a
  rw [map_one, one_mul]

theorem extendIntegralAction_end_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : NumberField.RingOfIntegers E →+* Module.End ℚ V)
    (a : NumberField.RingOfIntegers E) (v : V) :
    extendIntegralAction (D := Module.End ℚ V) ρ (a : E) v = ρ a v :=
  LinearMap.congr_fun (extendIntegralAction_integer (D := Module.End ℚ V) ρ a) v

theorem extendIntegralAction_end_commute_apply {V : Type*} [AddCommGroup V] [Module ℚ V]
    (ρ : NumberField.RingOfIntegers E →+* Module.End ℚ V) (F : Module.End ℚ V)
    (h : ∀ a, Commute (ρ a) F) (a : E) (v : V) :
    F (extendIntegralAction (D := Module.End ℚ V) ρ a v) =
      extendIntegralAction (D := Module.End ℚ V) ρ a (F v) :=
  (LinearMap.congr_fun (extendIntegralAction_commute ρ F h a).eq v).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ActionExtension
