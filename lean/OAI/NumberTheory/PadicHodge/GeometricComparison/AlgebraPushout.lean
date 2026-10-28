import OAI.NumberTheory.PadicHodge.GeometricComparison.QuotientModule
import Mathlib.RingTheory.IsTensorProduct

/-! # Algebra Pushout -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraPushout.AlgebraPushoutReduction

noncomputable section

/-! Actual ring pushouts preserve surjectivity and the extended reduction kernel. -/

open scoped TensorProduct

universe u v w
variable (R S : Type u) (A : Type v) (B : Type w) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [Algebra A B]
  [IsScalarTower R S B] [IsScalarTower R A B] [Algebra.IsPushout R S A B]
  (hS : Function.Surjective (algebraMap R S))

include hS in
theorem surjective : Function.Surjective (algebraMap A B) := by
  exact QuotientModule.QuotientModuleBaseChange.surjective R S
    (IsScalarTower.toAlgHom R A B).toLinearMap
    (Algebra.IsPushout.out (R := R) (S := S) (R' := A) (S' := B)) hS

include hS in
theorem kernel : RingHom.ker (algebraMap A B) =
    (RingHom.ker (algebraMap R S)).map (algebraMap R A) := by
  have h := QuotientModule.QuotientModuleBaseChange.ker_eq R S
    (IsScalarTower.toAlgHom R A B).toLinearMap
    (Algebra.IsPushout.out (R := R) (S := S) (R' := A) (S' := B)) hS
  rw [Ideal.smul_top_eq_map] at h
  exact SetLike.ext (fun a => SetLike.ext_iff.mp h a)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.AlgebraPushout.AlgebraPushoutReduction
