import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Variable Powers -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.VariablePowers.GradedHilbert

noncomputable section

/-! Arbitrary, possibly inhomogeneous elements of a projective saturation are killed modulo the original ideal by variable powers. -/

open _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem projectiveSaturation_le_variableLocalization (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) :
    (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal ≤
      (I.toIdeal.map (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i)))).comap
        (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Localization.Away (X (R := R) i))) := by
  let J := Projective.Saturation.GradedHilbert.projectiveSaturation I
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists (Hilbert.Polynomial.GradedHilbert.grading R n) J.toIdeal).mp J.isHomogeneous
  change J.toIdeal ≤ _
  rw [hS]
  apply Ideal.span_le.mpr
  rintro f ⟨g, hg, rfl⟩
  obtain ⟨d, hgd⟩ := g.property
  have hgj : g.val ∈ J.toIdeal := by
    rw [hS]
    exact Ideal.subset_span ⟨g, hg, rfl⟩
  obtain ⟨k, hk⟩ := (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff I hgd).mp hgj i
  apply (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (X i))
    (Localization.Away (X (R := R) i)) I.toIdeal g.val).mpr
  exact ⟨X i ^ k, ⟨k, rfl⟩, hk⟩

theorem projectiveSaturation_variable_power (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (hf : f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal) (i : Fin (n + 1)) :
    ∃ k : ℕ, X i ^ k * f ∈ I.toIdeal := by
  have h := projectiveSaturation_le_variableLocalization I i hf
  obtain ⟨s, hs, hsf⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers (X i))
    (Localization.Away (X (R := R) i)) I.toIdeal f).mp h
  obtain ⟨k, hk⟩ := hs
  refine ⟨k, ?_⟩
  rw [← hk] at hsf
  exact hsf

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.VariablePowers.GradedHilbert
