import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Regular.Flat
import Mathlib.Data.List.Nodup

/-! # Polynomial Regular Sequence -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularSequence.Constructions

noncomputable section

/-! Distinct polynomial coordinates form a regular sequence. The proof
uses the monomial coefficients of the actual polynomial ring, and flat
base change supplies regular equations in geometric coordinate rings. -/

open RingTheory.Sequence

variable {R σ : Type*} [CommRing R]

theorem mem_span_X_of_mul_mem (s : Set σ) (j : σ) (hj : j ∉ s)
    (f : MvPolynomial σ R)
    (hf : MvPolynomial.X j * f ∈ Ideal.span (MvPolynomial.X '' s)) :
    f ∈ Ideal.span (MvPolynomial.X '' s) := by
  classical
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro m hm
  have hmul : m + Finsupp.single j 1 ∈ (MvPolynomial.X j * f).support := by
    rw [MvPolynomial.mem_support_iff, mul_comm (MvPolynomial.X j) f,
      MvPolynomial.coeff_mul_X]
    exact MvPolynomial.mem_support_iff.mp hm
  obtain ⟨i, hi, hmi⟩ := MvPolynomial.mem_ideal_span_X_image.mp hf _ hmul
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  refine ⟨i, hi, ?_⟩
  simpa only [Finsupp.add_apply, Finsupp.single_eq_of_ne hij, add_zero] using hmi

theorem variable_regular_mod_other_variables (s : Set σ) (j : σ) (hj : j ∉ s) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span (MvPolynomial.X (R := R) '' s))
      (MvPolynomial.X j : MvPolynomial σ R) := by
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro f hf
  exact mem_span_X_of_mul_mem s j hj f hf

theorem ideal_ofList_variables (ls : List σ) :
    Ideal.ofList (ls.map (MvPolynomial.X : σ → MvPolynomial σ R)) =
      Ideal.span (MvPolynomial.X '' {j | j ∈ ls}) := by
  apply congrArg Ideal.span
  ext f
  simp

theorem variables_weaklyRegular (ls : List σ) (hl : ls.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (ls.map (MvPolynomial.X (R := R))) := by
  constructor
  intro i hi
  have hi' : i < ls.length := by simpa only [List.length_map] using hi
  rw [List.getElem_map, ← List.map_take]
  have he : (Ideal.ofList ((ls.take i).map (MvPolynomial.X (R := R))) •
      ⊤ : Submodule (MvPolynomial σ R) (MvPolynomial σ R)) =
      Ideal.span (MvPolynomial.X (R := R) '' {j | j ∈ ls.take i}) := by
    change Ideal.ofList ((ls.take i).map (MvPolynomial.X (R := R))) *
      (⊤ : Ideal (MvPolynomial σ R)) = _
    rw [Ideal.mul_top, ideal_ofList_variables]
  rw [he]
  apply variable_regular_mod_other_variables
  intro hh
  obtain ⟨j, hj, hej⟩ := List.mem_take_iff_getElem.mp hh
  have hji := hl.getElem_inj_iff.mp hej
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Thom.PolynomialRegularSequence.Constructions
