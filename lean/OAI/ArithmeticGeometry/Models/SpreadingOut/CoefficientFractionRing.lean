import OAI.ArithmeticGeometry.Models.CoefficientSystem
import Mathlib.RingTheory.Localization.FractionRing

/-! # Coefficient Fraction Ring -/

namespace OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientFractionRing.Construction

noncomputable section

/-! Coefficient subalgebras of a fraction field share that fraction field;
a nonzero coefficient becomes a unit at a later finite stage. -/

open scoped nonZeroDivisors

universe u

open OAI.ArithmeticGeometry.Models.CoefficientSystem.Constructions.Foundations

theorem subalgebra_fractionRing
    (R K : Type u) [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K] (A : Subalgebra R K) : IsFractionRing A K where
  map_units s := IsUnit.mk0 _ (by
    change (s.val : K) ≠ 0
    exact fun h ↦ nonZeroDivisors.coe_ne_zero s (Subtype.ext h))
  surj x := by
    obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj R⁰ x
    have hs0 : algebraMap R A (s : R) ≠ 0 := by
      intro h
      have H := congrArg (algebraMap A K) h
      change algebraMap R K (s : R) = 0 at H
      exact nonZeroDivisors.coe_ne_zero s
        ((IsFractionRing.injective R K) (H.trans (map_zero _).symm))
    refine ⟨⟨algebraMap R A a, ⟨algebraMap R A s, mem_nonZeroDivisors_of_ne_zero hs0⟩⟩, ?_⟩
    change x * algebraMap R K (s : R) = algebraMap R K a
    exact hs
  exists_of_eq {a b} h := by
    refine ⟨1, ?_⟩
    simpa only [OneMemClass.coe_one, one_mul] using (Subtype.ext h : a = b)

theorem subalgebra_element_isUnit_of_inverse_mem
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (A : Subalgebra R K) (a : A) (ha : a ≠ 0) (hi : (a : K)⁻¹ ∈ A) : IsUnit a := by
  have ha' : (a : K) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  refine ⟨⟨a, ⟨(a : K)⁻¹, hi⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (mul_inv_cancel₀ ha')
  · exact Subtype.ext (inv_mul_cancel₀ ha')

theorem coefficient_inverse_mem_later_stage
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing R K s) :
    ∃ (t : Finset K) (_ : s ⊆ t), (a : K)⁻¹ ∈ CoefficientSystem.Constructions.Foundations.coefficientRing R K t := by
  classical
  exact ⟨s ∪ {(a : K)⁻¹}, Finset.subset_union_left,
    Algebra.subset_adjoin (Finset.mem_union_right _ (Finset.mem_singleton_self _))⟩

theorem coefficientRingInclusion_exists
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {s t : Finset K} (h : s ⊆ t) :
    ∃ f : CoefficientSystem.Constructions.Foundations.coefficientRing R K s →+* CoefficientSystem.Constructions.Foundations.coefficientRing R K t,
      ∀ a, (f a : K) = (a : K) := by
  exact ⟨(Subalgebra.inclusion (Algebra.adjoin_mono (Finset.coe_subset.mpr h))).toRingHom,
    fun a ↦ Subalgebra.coe_inclusion _ a⟩

def coefficientRingInclusion
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {s t : Finset K} (h : s ⊆ t) : CoefficientSystem.Constructions.Foundations.coefficientRing R K s →+* CoefficientSystem.Constructions.Foundations.coefficientRing R K t :=
  Classical.choose (coefficientRingInclusion_exists R K h)

@[simp]
theorem coefficientRingInclusion_coe
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {s t : Finset K} (h : s ⊆ t) (a : CoefficientSystem.Constructions.Foundations.coefficientRing R K s) :
    (coefficientRingInclusion R K h a : K) = (a : K) :=
  Classical.choose_spec (coefficientRingInclusion_exists R K h) a

theorem coefficient_element_becomes_unit
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    (s : Finset K) (a : CoefficientSystem.Constructions.Foundations.coefficientRing R K s) (ha : a ≠ 0) :
    ∃ (t : Finset K) (h : s ⊆ t),
      IsUnit (coefficientRingInclusion R K h a) := by
  obtain ⟨t, h, hinv⟩ := coefficient_inverse_mem_later_stage R K s a
  let f := coefficientRingInclusion R K h
  refine ⟨t, h, subalgebra_element_isUnit_of_inverse_mem R K _ (f a) ?_ ?_⟩
  · intro he
    apply ha
    apply Subtype.ext
    have H := congrArg (fun x : CoefficientSystem.Constructions.Foundations.coefficientRing R K t ↦ (x : K)) he
    simpa only [f, coefficientRingInclusion_coe, Subalgebra.coe_zero] using H
  · change (coefficientRingInclusion R K h a : K)⁻¹ ∈ CoefficientSystem.Constructions.Foundations.coefficientRing R K t
    rw [coefficientRingInclusion_coe]
    exact hinv

end

end OAI.ArithmeticGeometry.Models.SpreadingOut.CoefficientFractionRing.Construction
