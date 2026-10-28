import OAI.NumberTheory.PadicHodge.IntegralComparison.StandardEtaleLiftAlgebra
import Mathlib.RingTheory.Polynomial.Basic

/-! # Standard Etale Lift -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.StandardEtaleLift

noncomputable section

/-! Lift an actual standard étale coordinate algebra through a
surjective coefficient map. The resulting smooth algebra has exactly
the prescribed quotient, including its coefficient action. -/

universe u v

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (h : Function.Surjective (algebraMap R S))
  (σ : Type v) (C : Type u) [Finite σ] [CommRing C]
  [Algebra S C] [Algebra (MvPolynomial σ S) C]
  [IsScalarTower S (MvPolynomial σ S) C]
  (P : StandardEtalePresentation (MvPolynomial σ S) C)

instance polynomialAlgebra : Algebra (MvPolynomial σ R) (MvPolynomial σ S) :=
  (MvPolynomial.map (algebraMap R S)).toAlgebra

omit [Finite σ] in
include h in
theorem polynomial_surjective :
    Function.Surjective (algebraMap (MvPolynomial σ R) (MvPolynomial σ S)) :=
  MvPolynomial.map_surjective (algebraMap R S) h

abbrev Ring := StandardEtaleLiftAlgebra.Ring (MvPolynomial σ S)
  (polynomial_surjective R S h σ) P.P

instance coefficientAlgebra : Algebra R (Ring R S h σ C P) :=
  ((algebraMap (MvPolynomial σ R) (Ring R S h σ C P)).comp MvPolynomial.C).toAlgebra

instance coefficientTower : IsScalarTower R (MvPolynomial σ R) (Ring R S h σ C P) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

instance smooth : Algebra.Smooth R (Ring R S h σ C P) := by
  let : Fintype σ := Fintype.ofFinite σ
  let : Algebra.Smooth R (MvPolynomial σ R) := ⟨inferInstance, inferInstance⟩
  exact Algebra.Smooth.comp R (MvPolynomial σ R) (Ring R S h σ C P)

instance flat : Module.Flat R (Ring R S h σ C P) := Algebra.Smooth.flat R (Ring R S h σ C P)

def reduction : Ring R S h σ C P →+* C :=
  P.equivRing.symm.toRingHom.comp
    (StandardEtaleLiftAlgebra.reduction (MvPolynomial σ S) (polynomial_surjective R S h σ) P.P)

omit [Finite σ] [Algebra S C] [IsScalarTower S (MvPolynomial σ S) C] in
theorem reduction_surjective : Function.Surjective (reduction R S h σ C P) :=
  P.equivRing.symm.surjective.comp
    (StandardEtaleLiftAlgebra.reduction_surjective (MvPolynomial σ S)
      (polynomial_surjective R S h σ) P.P)

omit [Finite σ] in
theorem reduction_base (r : R) :
    reduction R S h σ C P (algebraMap R (Ring R S h σ C P) r) =
      algebraMap S C (algebraMap R S r) := by
  change P.equivRing.symm
    (StandardEtaleLiftAlgebra.reduction (MvPolynomial σ S) (polynomial_surjective R S h σ) P.P
      (algebraMap (MvPolynomial σ R) (Ring R S h σ C P) (MvPolynomial.C r))) = _
  rw [StandardEtaleLiftAlgebra.reduction_base, P.equivRing.symm.commutes]
  change algebraMap (MvPolynomial σ S) C (MvPolynomial.map (algebraMap R S) (MvPolynomial.C r)) = _
  rw [MvPolynomial.map_C]
  exact (IsScalarTower.algebraMap_apply S (MvPolynomial σ S) C (algebraMap R S r)).symm

omit [Finite σ] [Algebra S C] [IsScalarTower S (MvPolynomial σ S) C] in
theorem reduction_kernel : RingHom.ker (reduction R S h σ C P) =
    (RingHom.ker (algebraMap R S)).map (algebraMap R (Ring R S h σ C P)) := by
  have he : RingHom.ker (reduction R S h σ C P) =
      RingHom.ker (StandardEtaleLiftAlgebra.reduction (MvPolynomial σ S)
        (polynomial_surjective R S h σ) P.P) :=
    RingHom.ker_comp_of_injective _ (show Function.Injective P.equivRing.symm.toRingHom from
      P.equivRing.symm.injective)
  rw [he, StandardEtaleLiftAlgebra.reduction_kernel]
  change (RingHom.ker (MvPolynomial.map (algebraMap R S))).map
    (algebraMap (MvPolynomial σ R) (Ring R S h σ C P)) = _
  rw [MvPolynomial.ker_map, Ideal.map_map]
  rfl

def quotientEquiv :
    (Ring R S h σ C P ⧸ (RingHom.ker (algebraMap R S)).map
      (algebraMap R (Ring R S h σ C P))) ≃+* C :=
  (Ideal.quotEquivOfEq (reduction_kernel R S h σ C P).symm).trans
    (RingHom.quotientKerEquivOfSurjective (reduction_surjective R S h σ C P))

omit [Finite σ] [Algebra S C] [IsScalarTower S (MvPolynomial σ S) C] in
theorem quotientEquiv_mk (a : Ring R S h σ C P) :
    quotientEquiv R S h σ C P
      (Ideal.Quotient.mk ((RingHom.ker (algebraMap R S)).map
        (algebraMap R (Ring R S h σ C P))) a) = reduction R S h σ C P a := by
  change (RingHom.quotientKerEquivOfSurjective (reduction_surjective R S h σ C P))
    ((Ideal.quotEquivOfEq (reduction_kernel R S h σ C P).symm) (Ideal.Quotient.mk _ a)) = _
  rw [Ideal.quotEquivOfEq_mk]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Polynomial.StandardEtaleLift
