import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealLocalization

/-! # Fraction Field Homogeneous Contraction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.FractionFieldHomogeneousContraction.GradedHilbert

noncomputable section

/-! Fraction-field extension detects homogeneous ideal membership after
clearing one nonzero coefficient denominator. Torsion-free degree quotients
therefore recover the entire ideal by contraction. -/

open _root_.MvPolynomial
open scoped nonZeroDivisors

universe u v
variable {R : Type u} [CommRing R] [IsDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

theorem fractionField_mem_extended_iff (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    MvPolynomial.map (algebraMap R K) f ∈ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal ↔
      ∃ r : R, r ≠ 0 ∧ C r * f ∈ I.toIdeal := by
  let : Algebra (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) := MvPolynomial.algebraMvPolynomial
  change algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n) f ∈
    I.toIdeal.map (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing K n)) ↔ _
  rw [IsLocalization.algebraMap_mem_map_algebraMap_iff (R⁰.map (MvPolynomial.C (σ := Fin (n + 1))))]
  constructor
  · rintro ⟨s, hs, hsf⟩
    obtain ⟨r, hr, rfl⟩ := hs
    exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hsf⟩
  · rintro ⟨r, hr, hrf⟩
    exact ⟨C r, ⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr, rfl⟩, hrf⟩

theorem contracted_extended_eq_of_degree_torsionFree (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (hT : ∀ d, Module.IsTorsionFree R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)) :
    ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I) = I := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  change MvPolynomial.map (algebraMap R K) f ∈ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal ↔ f ∈ I.toIdeal
  constructor
  · intro h
    obtain ⟨r, hr, hrf⟩ := (fractionField_mem_extended_iff (K := K) I f).mp h
    let := hT d
    let q := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
    let v : Hilbert.Polynomial.GradedHilbert.grading R n d := ⟨f, hf⟩
    have hz : r • q.mkQ v = 0 := by
      rw [← map_smul]
      apply (Submodule.Quotient.mk_eq_zero q).mpr
      change r • f ∈ I.toIdeal
      rw [Algebra.smul_def]
      exact hrf
    have hv : q.mkQ v = 0 := (smul_eq_zero.mp hz).resolve_left hr
    exact (Submodule.Quotient.mk_eq_zero q).mp hv
  · exact Ideal.mem_map_of_mem (MvPolynomial.map (algebraMap R K))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.FractionFieldHomogeneousContraction.GradedHilbert
