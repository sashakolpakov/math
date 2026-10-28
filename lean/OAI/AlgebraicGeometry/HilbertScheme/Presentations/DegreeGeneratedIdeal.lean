import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Degree Generated Ideal -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert

noncomputable section

/-! Generation by a single homogeneous degree and its relation to a bound on generator degrees. -/

open _root_.MvPolynomial DirectSum

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

def degreeGeneratedIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ) : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) where
  __ := Ideal.span {f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n | f ∈ Hilbert.Polynomial.GradedHilbert.grading R n N ∧ f ∈ I.toIdeal}
  is_homogeneous' := Ideal.homogeneous_span (Hilbert.Polynomial.GradedHilbert.grading R n) _ (fun _ hf => ⟨N, hf.1⟩)

theorem degreeGeneratedIdeal_le (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ) :
    (degreeGeneratedIdeal I N).toIdeal ≤ I.toIdeal := Ideal.span_le.mpr (fun _ hf => hf.2)

theorem mem_degreeGeneratedIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hf : f ∈ Hilbert.Polynomial.GradedHilbert.grading R n N) (hI : f ∈ I.toIdeal) :
    f ∈ (degreeGeneratedIdeal I N).toIdeal := Ideal.subset_span ⟨hf, hI⟩

theorem homogeneous_multiple_mem_degreeGeneratedIdeal (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N e k : ℕ)
    (b c : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hb : b ∈ Hilbert.Polynomial.GradedHilbert.grading R n e) (hbI : b ∈ I.toIdeal) (he : e ≤ N)
    (hc : c ∈ Hilbert.Polynomial.GradedHilbert.grading R n k) (hNk : N ≤ k + e) : c * b ∈ (degreeGeneratedIdeal I N).toIdeal := by
  classical
  rw [← c.support_sum_monomial_coeff, Finset.sum_mul]
  apply Ideal.sum_mem
  intro a ha
  have had : a.degree = k := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support c k).mp hc a ha
  obtain ⟨z, hza, hz⟩ := Finsupp.exists_le_degree_eq a (N - e) (by omega)
  have hgen : monomial z (1 : R) * b ∈ (degreeGeneratedIdeal I N).toIdeal := by
    apply mem_degreeGeneratedIdeal I N
    · have hhom := (isHomogeneous_monomial (1 : R) hz).mul hb
      change (monomial z (1 : R) * b).IsHomogeneous N
      simpa only [Nat.sub_add_cancel he] using hhom
    · exact I.toIdeal.mul_mem_left _ hbI
  have hfactor : monomial a (c.coeff a) * b =
      monomial (a - z) (c.coeff a) * (monomial z (1 : R) * b) := by
    rw [← mul_assoc, monomial_mul_monomial, mul_one, tsub_add_cancel_of_le hza]
  rw [hfactor]
  exact (degreeGeneratedIdeal I N).toIdeal.mul_mem_left _ hgen

theorem degreeGeneratedIdeal_eventual_relations (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)
    (B : Finset (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) (hB : I.toIdeal = Ideal.span (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)))
    (hdeg : ∀ b ∈ B, ∃ e ≤ N, b ∈ Hilbert.Polynomial.GradedHilbert.grading R n e) (d : ℕ) (hd : N ≤ d) :
    Hilbert.Polynomial.GradedHilbert.degreeRelations (degreeGeneratedIdeal I N).toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  classical
  apply le_antisymm
  · exact Hilbert.Polynomial.GradedHilbert.degreeRelations_mono (degreeGeneratedIdeal_le I N) d
  · intro f hf
    have hfspan : f.val ∈ Submodule.span (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (B : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
      have hfI : f.val ∈ I.toIdeal := hf
      rw [hB] at hfI
      exact hfI
    obtain ⟨c, _, hc⟩ := Submodule.mem_span_finset.mp hfspan
    have hp : GradedRing.proj (Hilbert.Polynomial.GradedHilbert.grading R n) d f.val = f.val := by
      rw [GradedRing.proj_apply, decompose_of_mem_same (Hilbert.Polynomial.GradedHilbert.grading R n) f.property]
    change f.val ∈ (degreeGeneratedIdeal I N).toIdeal
    rw [← hp, ← hc, map_sum]
    apply Ideal.sum_mem
    intro b hbB
    obtain ⟨e, he, hb⟩ := hdeg b hbB
    change (decompose (Hilbert.Polynomial.GradedHilbert.grading R n) (c b * b) d).val ∈ (degreeGeneratedIdeal I N).toIdeal
    rw [coe_decompose_mul_of_right_mem_of_le (Hilbert.Polynomial.GradedHilbert.grading R n) hb (he.trans hd)]
    have hbI : b ∈ I.toIdeal := by
      rw [hB]
      exact Ideal.subset_span hbB
    exact homogeneous_multiple_mem_degreeGeneratedIdeal I N e (d - e) b
      (decompose (Hilbert.Polynomial.GradedHilbert.grading R n) (c b) (d - e)).val hb hbI he
      (decompose (Hilbert.Polynomial.GradedHilbert.grading R n) (c b) (d - e)).property (by omega)

theorem degreeGeneratedIdeal_eq_of_degreeRelations_eq
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (N : ℕ)
    (h : Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N) :
    degreeGeneratedIdeal I N = degreeGeneratedIdeal J N := by
  apply HomogeneousIdeal.ext
  apply congrArg Ideal.span
  apply Set.ext
  intro f
  constructor
  · rintro ⟨hf, hI⟩
    have hm : (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n N) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal N := hI
    rw [h] at hm
    exact ⟨hf, hm⟩
  · rintro ⟨hf, hJ⟩
    have hm : (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n N) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal N := hJ
    rw [← h] at hm
    exact ⟨hf, hm⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert
