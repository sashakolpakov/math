import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.IsTensorProduct

/-! # Surjective Ring Pushout -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.SurjectiveRingPushout

noncomputable section

/-! A commutative square of surjections is a ring pushout when the bottom kernel is the extended top kernel. -/

open scoped TensorProduct

variable {A B S T : Type} [CommRing A] [CommRing B] [CommRing S] [CommRing T]
  [Algebra A B] [Algebra A S] [Algebra A T] [Algebra B T] [Algebra S T]
  [IsScalarTower A B T] [IsScalarTower A S T]

theorem isPushout_of_surjective_kernel
    (hAB : Function.Surjective (algebraMap A B))
    (hST : Function.Surjective (algebraMap S T))
    (hker : RingHom.ker (algebraMap S T) =
      Ideal.map (algebraMap A S) (RingHom.ker (algebraMap A B))) :
    Algebra.IsPushout A S B T := by
  let I := RingHom.ker (algebraMap A B)
  let J := Ideal.map (algebraMap A S) I
  have hJ : ∀ s : S, s ∈ J → algebraMap S T s = 0 := by
    intro s hs
    exact (show J ≤ RingHom.ker (algebraMap S T) from hker.ge) hs
  let q : S ⧸ J →ₐ[S] T := Ideal.Quotient.liftₐ J (Algebra.ofId S T) hJ
  have hq : Function.Bijective q := by
    constructor
    · exact RingHom.lift_injective_of_ker_le_ideal J hJ hker.le
    · intro t
      obtain ⟨s, rfl⟩ := hST t
      exact ⟨Ideal.Quotient.mk J s, rfl⟩
  let eB : (A ⧸ I) ≃ₐ[A] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) hAB
  let e : S ⊗[A] B ≃ₐ[S] T :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eB.symm).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.trans
        (AlgEquiv.ofBijective q hq))
  constructor
  apply IsBaseChange.of_equiv e.toLinearEquiv
  intro b
  obtain ⟨a, rfl⟩ := hAB b
  change e (1 ⊗ₜ[A] algebraMap A B a) = algebraMap B T (algebraMap A B a)
  have heB : eB.symm (algebraMap A B a) = Ideal.Quotient.mk I a :=
    Ideal.quotientKerAlgEquivOfSurjective_symm_apply hAB a
  change q ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) eB.symm)
      (1 ⊗ₜ[A] algebraMap A B a))) = _
  rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
  change q ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
    (1 ⊗ₜ[A] eB.symm (algebraMap A B a))) = _
  rw [heB, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  change algebraMap S T (a • (1 : S)) = algebraMap B T (algebraMap A B a)
  rw [← Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_apply A S T,
    ← IsScalarTower.algebraMap_apply A B T]

end

end OAI.AlgebraicGeometry.Comparison.Betti.SurjectiveRingPushout
