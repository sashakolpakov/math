import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLift
import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleBaseChange
import OAI.NumberTheory.PadicHodge.IntegralComparison.SurjectiveBaseChange
import Mathlib.RingTheory.Smooth.Flat

/-! # Standard Etale Lift Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra

noncomputable section

/-! The actual lifted standard etale algebra is flat and has its original special fibre. -/

open _root_.Polynomial

universe u v

open scoped TensorProduct

private def baseChangeEquiv {R : Type u} [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] (Q : StandardEtalePair R) :
    S ⊗[R] Q.Ring ≃ₐ[S] (Q.map (algebraMap R S)).Ring :=
  ((StandardEtaleBaseChange.presentation Q).baseChange (T := S)).equivRing

private def baseChangeMap {R : Type u} [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] (Q : StandardEtalePair R) :
    Q.Ring →+* (Q.map (algebraMap R S)).Ring :=
  (baseChangeEquiv S Q).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom

private theorem baseChangeMap_surjective {R : Type u} [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] (Q : StandardEtalePair R)
    (h : Function.Surjective (algebraMap R S)) : Function.Surjective (baseChangeMap S Q) := by
  apply (baseChangeEquiv S Q).surjective.comp
  intro x
  obtain ⟨z, hz⟩ := (SurjectiveBaseChange.quotientEquiv S Q.Ring h).surjective x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨a, (SurjectiveBaseChange.quotientEquiv_mk S Q.Ring h a).symm.trans hz⟩

private theorem baseChangeMap_base {R : Type u} [CommRing R] (S : Type v)
    [CommRing S] [Algebra R S] (Q : StandardEtalePair R) (r : R) :
    baseChangeMap S Q (algebraMap R Q.Ring r) =
      algebraMap S (Q.map (algebraMap R S)).Ring (algebraMap R S r) := by
  change baseChangeEquiv S Q (1 ⊗ₜ[R] algebraMap R Q.Ring r) = _
  rw [← Algebra.TensorProduct.algebraMap_apply',
    IsScalarTower.algebraMap_eq R S (S ⊗[R] Q.Ring), RingHom.comp_apply]
  exact (baseChangeEquiv S Q).commutes _

variable {R : Type u} [CommRing R] (S : Type v) [CommRing S] [Algebra R S]
  (h : Function.Surjective (algebraMap R S)) (P : StandardEtalePair S)

abbrev Ring := (StandardEtaleLift.pair (algebraMap R S) h P).Ring

instance etale : Algebra.Etale R (StandardEtaleLiftAlgebra.Ring S h P) := inferInstanceAs
  (Algebra.Etale R (StandardEtaleLift.pair (algebraMap R S) h P).Ring)

instance flat : Module.Flat R (StandardEtaleLiftAlgebra.Ring S h P) := Algebra.Smooth.flat R (StandardEtaleLiftAlgebra.Ring S h P)

def reduction : StandardEtaleLiftAlgebra.Ring S h P →+* P.Ring :=
  (StandardEtaleLift.residueEquiv (algebraMap R S) h P).toRingHom.comp
    (baseChangeMap S (StandardEtaleLift.pair (algebraMap R S) h P))

theorem reduction_surjective : Function.Surjective (reduction S h P) :=
  (StandardEtaleLift.residueEquiv (algebraMap R S) h P).surjective.comp
    (baseChangeMap_surjective S (StandardEtaleLift.pair (algebraMap R S) h P) h)

theorem reduction_base (r : R) : reduction S h P (algebraMap R (StandardEtaleLiftAlgebra.Ring S h P) r) =
    algebraMap S P.Ring (algebraMap R S r) := by
  change StandardEtaleLift.residueEquiv (algebraMap R S) h P
    (baseChangeMap S (StandardEtaleLift.pair (algebraMap R S) h P)
      (algebraMap R (StandardEtaleLiftAlgebra.Ring S h P) r)) = _
  rw [baseChangeMap_base]
  exact (StandardEtaleLift.residueEquiv (algebraMap R S) h P).commutes _

theorem reduction_kernel : RingHom.ker (reduction S h P) =
    (RingHom.ker (algebraMap R S)).map (algebraMap R (StandardEtaleLiftAlgebra.Ring S h P)) := by
  have h₁ : RingHom.ker (reduction S h P) =
      RingHom.ker (baseChangeMap S (StandardEtaleLift.pair (algebraMap R S) h P)) :=
    RingHom.ker_comp_of_injective _
      (show Function.Injective (StandardEtaleLift.residueEquiv (algebraMap R S) h P).toRingHom from
        (StandardEtaleLift.residueEquiv (algebraMap R S) h P).injective)
  have h₂ : RingHom.ker (baseChangeMap S
      (StandardEtaleLift.pair (algebraMap R S) h P)) =
      RingHom.ker (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := StandardEtaleLiftAlgebra.Ring S h P)).toRingHom :=
    RingHom.ker_comp_of_injective _
      (show Function.Injective (baseChangeEquiv S
          (StandardEtaleLift.pair (algebraMap R S) h P)).toRingHom from
        (baseChangeEquiv S (StandardEtaleLift.pair (algebraMap R S) h P)).injective)
  exact h₁.trans (h₂.trans (SurjectiveBaseChange.kernel S (StandardEtaleLiftAlgebra.Ring S h P) h))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra
