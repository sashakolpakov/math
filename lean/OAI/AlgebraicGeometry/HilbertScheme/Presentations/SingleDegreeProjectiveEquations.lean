import OAI.AlgebraicGeometry.HilbertScheme.Presentations.FinitelyGeneratedHomogeneousIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.ChartIdeals
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.GeneratedDegreeRelations

/-! # Single Degree Projective Equations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeProjectiveEquations.GradedHilbert

noncomputable section

/-! Every finitely generated homogeneous ideal has finite equations of one
common degree defining exactly the same projective closed subscheme. -/

open _root_.AlgebraicGeometry _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem finite_single_degree_projective_equations (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hfg : I.toIdeal.FG) :
    ∃ (m N : ℕ) (g : Fin m → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hg : ∀ j, (g j).IsHomogeneous N),
      Projective.Saturation.GradedHilbert.projectiveSaturation (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) = Projective.Saturation.GradedHilbert.projectiveSaturation I := by
  classical
  obtain ⟨t, ht, hhom⟩ := FinitelyGeneratedHomogeneousIdeals.GradedHilbert.fg_homogeneous_generating_finset I hfg
  choose d hd using fun j : t => hhom j.val j.property
  let N := Finset.univ.sup d
  have hdN (j : t) : d j ≤ N := Finset.le_sup (Finset.mem_univ j)
  let g : t × Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n := fun j => X j.2 ^ (N - d j.1) * j.1.val
  have hg (j : t × Fin (n + 1)) : (g j).IsHomogeneous N := by
    have hx : (X (R := R) j.2 ^ (N - d j.1)).IsHomogeneous (N - d j.1) := by
      simpa only [one_mul] using (isHomogeneous_X R j.2).pow (N - d j.1)
    simpa only [Nat.sub_add_cancel (hdN j.1)] using hx.mul (hd j.1)
  let J := Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg
  have hJ : J.toIdeal ≤ I.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact I.toIdeal.mul_mem_left _ (ht ▸ Ideal.subset_span j.1.property)
  have hc (i : Fin (n + 1)) : J.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) = I.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i) := by
    apply le_antisymm (Ideal.map_mono hJ)
    rw [← ht, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro _ ⟨f, hf, rfl⟩
    change Dehomogenization.GradedHilbert.dehomogenize i f ∈ J.toIdeal.map (Dehomogenization.GradedHilbert.dehomogenize i)
    have hm : g (⟨f, hf⟩, i) ∈ J.toIdeal := Ideal.subset_span ⟨(⟨f, hf⟩, i), rfl⟩
    have H := Ideal.mem_map_of_mem (Dehomogenization.GradedHilbert.dehomogenize i) hm
    simpa only [g, map_mul, map_pow, Dehomogenization.GradedHilbert.dehomogenize_self, one_pow, one_mul] using H
  let e : Fin (Fintype.card (t × Fin (n + 1))) ≃ t × Fin (n + 1) := (Fintype.equivFin _).symm
  have he : Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (fun j => g (e j)) N (fun j => hg (e j)) = J := by
    apply HomogeneousIdeal.ext
    change Ideal.span (Set.range (fun j => g (e j))) = Ideal.span (Set.range g)
    congr 1
    ext z
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨e.symm j, congrArg g (e.apply_symm_apply j)⟩
  refine ⟨Fintype.card (t × Fin (n + 1)), N, (fun j => g (e j)), (fun j => hg (e j)), ?_⟩
  rw [he]
  exact Saturation.ChartIdeals.GradedHilbert.projectiveSaturation_eq_of_dehomogenized J I hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SingleDegreeProjectiveEquations.GradedHilbert
