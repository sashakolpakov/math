import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.IdealGenerators
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.ChartEquationFiniteness

/-! # Homogeneous Chart Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomogeneousChartEquations.GradedHilbert

noncomputable section

/-! Finitely generated standard-chart ideals admit one finite homogeneous
subideal with exactly the same projective chart equations. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem finite_homogeneous_same_chart_ideals (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (hfg : ∀ i : Fin (n + 1), (I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)).FG) :
    ∃ J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n), J.toIdeal.FG ∧ J ≤ I ∧
      ∀ i : Fin (n + 1), J.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) = I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) := by
  classical
  obtain ⟨s, hs⟩ := (Ideal.IsHomogeneous.iff_exists (Hilbert.Polynomial.GradedHilbert.grading R n) I.toIdeal).mp I.isHomogeneous
  let S : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) := Subtype.val '' s
  have hS : Ideal.span S = I.toIdeal := hs.symm
  have hi (i : Fin (n + 1)) : ((Ideal.span S).map (Dehomogenization.GradedHilbert.dehomogenize i)).FG := hS.symm ▸ hfg i
  choose t ht he using fun i : Fin (n + 1) => IdealGenerators.fg_map_span_finite_subset (Dehomogenization.GradedHilbert.dehomogenize i) S (hi i)
  let w := Finset.univ.biUnion t
  have hw : (↑w : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) ⊆ S := by
    intro f hf
    obtain ⟨i, _, hfi⟩ := Finset.mem_biUnion.mp hf
    exact ht i hfi
  have hhom : (Ideal.span (↑w : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))).IsHomogeneous (Hilbert.Polynomial.GradedHilbert.grading R n) := by
    apply Ideal.homogeneous_span
    intro f hf
    obtain ⟨g, _, rfl⟩ := hw hf
    exact g.property
  let J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) := ⟨Ideal.span (↑w : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)), hhom⟩
  have hJI : J ≤ I := by
    change Ideal.span (↑w : Set (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) ≤ I.toIdeal
    rw [← hS]
    exact Ideal.span_mono hw
  refine ⟨J, Submodule.fg_span w.finite_toSet, hJI, ?_⟩
  intro i
  apply le_antisymm (Ideal.map_mono hJI)
  change I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) ≤ J.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)
  rw [← hS, ← he i]
  apply Ideal.map_mono
  apply Ideal.span_mono
  intro f hf
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hf⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.HomogeneousChartEquations.GradedHilbert
