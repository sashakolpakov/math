import OAI.ArithmeticGeometry.Models.SpreadingOut.CommonDenominator
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Common Open Algebra -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.CommonOpenAlgebra.Construction

noncomputable section

/-! A common denominator gives an explicit isomorphism of principal opens. -/

universe u

def subalgebra_common_open_iso
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (T : Subalgebra R A) (d : R) (hd : ∀ x : A, d • x ∈ T) :
    Localization.Away (algebraMap R T d) ≃ₐ[R]
      Localization.Away (algebraMap R A d) := by
  have hloc : IsLocalization.Away (T.val (algebraMap R T d))
      (Localization.Away (algebraMap R A d)) := by
    rw [T.val.commutes]
    infer_instance
  let f := IsLocalization.Away.mapₐ
    (Localization.Away (algebraMap R T d)) (Localization.Away (algebraMap R A d))
    T.val (algebraMap R T d)
  apply AlgEquiv.ofBijective f
  refine ⟨IsLocalization.Away.mapₐ_injective_of_injective (f := T.val) _
    (show Function.Injective T.val from Subtype.val_injective), ?_⟩
  apply (IsLocalization.Away.map_surjective_iff
    (Localization.Away (algebraMap R T d)) (Localization.Away (algebraMap R A d))
    T.val.toRingHom (algebraMap R T d)).mpr
  intro x
  refine ⟨⟨d • x, hd x⟩, 1, ?_⟩
  change d • x = (algebraMap R A d) ^ 1 * x
  rw [pow_one, Algebra.smul_def]

def localization_iso_of_algEquiv
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A ≃ₐ[R] B) (d : R) :
    Localization.Away (algebraMap R A d) ≃ₐ[R]
      Localization.Away (algebraMap R B d) :=
  IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers (algebraMap R A d))
    (T := Submonoid.powers (algebraMap R B d)) _ _ e (by
      rw [Submonoid.map_powers, e.commutes])

theorem finite_domain_common_hypersurface_open
    (P A F : Type u) [CommRing P] [IsDomain P] [IsIntegrallyClosed P]
    [CommRing A] [IsDomain A] [Field F] [CharZero F]
    [Algebra P A] [FaithfulSMul P A] [Algebra P F] [IsFractionRing P F]
    [Module.Finite P A] :
    ∃ (a : A) (d : P), d ≠ 0 ∧ Nonempty
      (Localization.Away (algebraMap P (AdjoinRoot (minpoly P a)) d) ≃ₐ[P]
        Localization.Away (algebraMap P A d)) := by
  obtain ⟨a, d, hd, hdx⟩ := CommonDenominator.Construction.finite_domain_primitive_common_denominator P A F
  let e := minpoly.equivAdjoin (Algebra.IsIntegral.isIntegral (R := P) a)
  exact ⟨a, d, hd, ⟨(localization_iso_of_algEquiv e d).trans
    (subalgebra_common_open_iso P A (Algebra.adjoin P {a}) d hdx)⟩⟩

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.CommonOpenAlgebra.Construction
