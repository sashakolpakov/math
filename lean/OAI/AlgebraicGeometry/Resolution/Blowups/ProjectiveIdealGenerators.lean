import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.EquivFin

/-! # Projective Ideal Generators -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveIdealGenerators.Construction

noncomputable section

/-! Common-degree homogeneous generators for ideal sheaves on projective space. -/

open _root_.MvPolynomial _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}

/-- A homogeneous ideal has finitely many homogeneous generators, each
with its actual degree. -/
theorem exists_finite_homogeneous_ideal_generators (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ∃ (s : Finset (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) (d : s → ℕ),
      (∀ p : s, p.val.IsHomogeneous (d p)) ∧ Ideal.span (s : Set (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) = I.toIdeal := by
  classical
  obtain ⟨H, hH⟩ := (Ideal.IsHomogeneous.iff_exists (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) I.toIdeal).mp I.isHomogeneous
  have hfg : (Ideal.span (Subtype.val '' H)).FG := hH ▸ IsNoetherian.noetherian I.toIdeal
  obtain ⟨s, hs, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset (Subtype.val '' H)).mp hfg
  have hhom : ∀ p : s, ∃ d : ℕ, p.val.IsHomogeneous d := by
    intro p
    obtain ⟨v, _, hv⟩ := hs p.property
    obtain ⟨d, hd⟩ := v.property
    exact ⟨d, hv ▸ hd⟩
  choose d hd using hhom
  exact ⟨s, d, hd, hspan.symm.trans hH.symm⟩

/-- Raising each generator to a common degree with powers of each chart
coordinate retains all dehomogenized ideals on every standard chart. -/
theorem exists_common_degree_projective_generators (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    ∃ (ι : Type u) (_ : Fintype ι) (D : ℕ) (p : ι → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n),
      0 < D ∧ (∀ j, (p j).IsHomogeneous D) ∧ (∀ j, p j ∈ I.toIdeal) ∧
        ∀ i : Fin (n + 1), Ideal.span (Set.range (fun j => HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (p j))) =
          I.toIdeal.map (HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i) := by
  classical
  obtain ⟨s, d, hhom, hgen⟩ := exists_finite_homogeneous_ideal_generators I
  let D := (Finset.univ.sup d) + 1
  have hd : ∀ j : s, d j ≤ D := fun j =>
    (Finset.le_sup (f := d) (Finset.mem_univ j)).trans (Nat.le_succ _)
  let p : Fin (n + 1) × s → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n := fun j =>
    X j.1 ^ (D - d j.2) * j.2.val
  have hmem : ∀ j, p j ∈ I.toIdeal := by
    intro j
    apply I.toIdeal.mul_mem_left
    rw [← hgen]
    exact Ideal.subset_span j.2.property
  refine ⟨Fin (n + 1) × s, inferInstance, D, p, Nat.zero_lt_succ _, ?_, hmem, ?_⟩
  · intro j
    simpa only [Nat.one_mul, Nat.sub_add_cancel (hd j.2)] using
      ((isHomogeneous_X R j.1).pow (D - d j.2)).mul (hhom j.2)
  · intro i
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.mem_map_of_mem _ (hmem j)
    · rw [← hgen, Ideal.map_span]
      apply Ideal.span_le.mpr
      rintro _ ⟨q, hq, rfl⟩
      have he : HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (p (i, ⟨q, hq⟩)) = HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i q := by
        simp only [p, map_mul, map_pow, HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize_self, one_pow, one_mul]
      rw [← he]
      exact Ideal.subset_span ⟨(i, ⟨q, hq⟩), rfl⟩

/-- Every projective ideal sheaf is generated on every standard affine
chart by the dehomogenizations of a finite family of forms of one positive degree. -/
theorem projective_idealSheaf_exists_common_degree_generators
    (J : (Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    ∃ (ι : Type u) (_ : Fintype ι) (D : ℕ) (p : ι → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n),
      0 < D ∧ (∀ j, (p j).IsHomogeneous D) ∧
        ∀ i : Fin (n + 1), Ideal.span (Set.range (fun j => HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (p j))) =
          HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J i := by
  obtain ⟨ι, hι, D, p, hD, hhom, _, hgen⟩ :=
    exists_common_degree_projective_generators (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf J)
  refine ⟨ι, hι, D, p, hD, hhom, ?_⟩
  intro i
  exact (hgen i).trans (HilbertScheme.Presentations.Projective.ChartOverlap.GradedHilbert.chartHomogeneousIdeal_map (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J)
    (HilbertScheme.Presentations.Projective.IdealEquivalence.GradedHilbert.projectiveChartIdeal_compatible J) i)

/-- Padding by a zero form gives an ordinary nonempty finite projective
coordinate family, including when the ideal sheaf is zero. -/
theorem projective_idealSheaf_exists_fin_common_degree_generators
    (J : (Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).IdealSheafData) :
    ∃ (m D : ℕ) (p : Fin (m + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n),
      0 < D ∧ (∀ j, (p j).IsHomogeneous D) ∧
        ∀ i : Fin (n + 1), Ideal.span (Set.range (fun j => HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (p j))) =
          HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J i := by
  classical
  obtain ⟨ι, hι, D, p, hD, hhom, hgen⟩ :=
    projective_idealSheaf_exists_common_degree_generators J
  let e : Option ι ≃ Fin (Fintype.card ι + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  let q : Option ι → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n := fun j => j.elim 0 p
  refine ⟨Fintype.card ι, D, q ∘ e.symm, hD, ?_, ?_⟩
  · intro j
    change (q (e.symm j)).IsHomogeneous D
    cases e.symm j with
    | none => exact (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n D).zero_mem
    | some j => exact hhom j
  · intro i
    change Ideal.span (Set.range ((fun j => HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i (q j)) ∘ e.symm)) = _
    rw [e.symm.surjective.range_comp]
    apply le_antisymm
    · apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      cases j with
      | none =>
        change HilbertScheme.Presentations.Dehomogenization.GradedHilbert.dehomogenize i 0 ∈ HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J i
        rw [map_zero]
        exact (HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.projectiveChartIdeal J i).zero_mem
      | some j =>
        rw [← hgen i]
        exact Ideal.subset_span ⟨j, rfl⟩
    · rw [← hgen i]
      apply Ideal.span_le.mpr
      rintro _ ⟨j, rfl⟩
      exact Ideal.subset_span ⟨some j, rfl⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveIdealGenerators.Construction
