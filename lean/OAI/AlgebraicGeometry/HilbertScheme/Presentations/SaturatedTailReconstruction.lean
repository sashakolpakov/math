import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Saturated Tail Reconstruction -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedTailReconstruction.GradedHilbert

noncomputable section

/-! A homogeneous subideal agreeing with a saturated ideal in all high
degrees has precisely that saturation, over an arbitrary coefficient ring. -/

open _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem projectiveSaturation_eq_of_le_eventual_relations
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hIJ : I ≤ J) (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal)
    (N : ℕ) (h : ∀ d ≥ N, Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d) :
    Projective.Saturation.GradedHilbert.projectiveSaturation I = J := by
  apply HomogeneousIdeal.ext'
  intro d f hf
  change f ∈ (Projective.Saturation.GradedHilbert.projectiveSaturation I).toIdeal ↔ f ∈ J.toIdeal
  constructor
  · intro hsat
    apply hJ.mem_of_variable_powers f d hf
    intro i
    obtain ⟨k, hk⟩ := (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff I hf).mp hsat i
    exact ⟨k, hIJ hk⟩
  · intro hfJ
    apply (Projective.Saturation.GradedHilbert.mem_projectiveSaturation_iff I hf).mpr
    intro i
    have hi : (X (R := R) i ^ N).IsHomogeneous N := by
      simpa only [one_mul] using (isHomogeneous_X R i).pow N
    have hm : (⟨X i ^ N * f, hi.mul hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n (N + d)) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal (N + d) :=
      J.toIdeal.mul_mem_left _ hfJ
    rw [← h (N + d) (by omega)] at hm
    exact ⟨N, hm⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedTailReconstruction.GradedHilbert
