import OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Regular.SequenceFlatBaseChange
import Mathlib.RingTheory.MvPolynomial.Ideal

/-! # Regular Sequence -/

namespace OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.RegularSequence

noncomputable section

/-! Distinct polynomial variables form a weakly regular sequence over
any coefficient ring. The proof checks injectivity modulo each preceding
variable ideal directly on monomial coefficients. -/

universe u v

open RingTheory.Sequence
open scoped Pointwise

variable (R : Type u) [CommRing R] (σ : Type v)

theorem variable_regular (s : Set σ) (i : σ) (hi : i ∉ s) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span (MvPolynomial.X (R := R) '' s)) (MvPolynomial.X (R := R) i) := by
  classical
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro f hf
  change MvPolynomial.X i * f ∈ Ideal.span (MvPolynomial.X '' s) at hf
  rw [MvPolynomial.mem_ideal_span_X_image] at hf ⊢
  intro d hd
  have hd' : Finsupp.single i 1 + d ∈ (MvPolynomial.X i * f).support := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_X_mul]
    exact MvPolynomial.mem_support_iff.mp hd
  obtain ⟨j, hj, hnonzero⟩ := hf _ hd'
  refine ⟨j, hj, ?_⟩
  have hji : i ≠ j := fun h => hi (h.symm ▸ hj)
  simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hji.symm, zero_add] using hnonzero

theorem ofList_variables (xs : List σ) :
    Ideal.ofList (xs.map (MvPolynomial.X : σ → MvPolynomial σ R)) =
      Ideal.span (MvPolynomial.X '' {i | i ∈ xs}) := by
  apply congrArg Ideal.span
  ext f
  exact List.mem_map

theorem weakly_regular (xs : List σ) (hx : xs.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (xs.map (MvPolynomial.X : σ → MvPolynomial σ R)) := by
  induction xs using List.reverseRecOn with
  | nil => exact IsWeaklyRegular.nil _ _
  | append_singleton xs i ih =>
    have hi : i ∉ xs := fun h => (List.nodup_append.mp hx).2.2 i h i (List.mem_singleton_self i) rfl
    have hxs : xs.Nodup := (List.nodup_append.mp hx).1
    rw [List.map_append, List.map_singleton, isWeaklyRegular_append_iff]
    refine ⟨ih hxs, ?_⟩
    rw [isWeaklyRegular_singleton_iff, smul_eq_mul, Ideal.mul_top, ofList_variables]
    exact variable_regular R σ {j | j ∈ xs} i hi

end

end OAI.AlgebraicGeometry.IntersectionTheory.ProjectionFormula.Polynomial.RegularSequence
