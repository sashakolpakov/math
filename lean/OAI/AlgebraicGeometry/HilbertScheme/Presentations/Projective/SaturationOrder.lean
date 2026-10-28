import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Saturation

/-! # Saturation Order -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationOrder.GradedHilbert

noncomputable section

/-! Projective saturation is the least saturated homogeneous ideal
containing the original ideal. -/

open _root_.MvPolynomial

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem projectiveSaturation_le_iff (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal) : Saturation.GradedHilbert.projectiveSaturation I ≤ J ↔ I ≤ J := by
  constructor
  · intro h
    exact (Saturation.GradedHilbert.le_projectiveSaturation I).trans h
  · intro h f hf
    apply (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading R n) J.isHomogeneous).mpr
    intro d
    let p := DirectSum.decompose (Hilbert.Polynomial.GradedHilbert.grading R n) f d
    have hp : p.val ∈ (Saturation.GradedHilbert.projectiveSaturation I).toIdeal :=
      (Ideal.IsHomogeneous.mem_iff (Hilbert.Polynomial.GradedHilbert.grading R n) (Saturation.GradedHilbert.projectiveSaturation I).isHomogeneous).mp hf d
    apply hJ.mem_of_variable_powers p.val d p.property
    intro i
    obtain ⟨k, hk⟩ := (Saturation.GradedHilbert.mem_projectiveSaturation_iff I p.property).mp hp i
    exact ⟨k, h hk⟩

theorem projectiveSaturation_mono : Monotone (Saturation.GradedHilbert.projectiveSaturation (R := R) (n := n)) := by
  intro I J h
  exact (projectiveSaturation_le_iff I (Saturation.GradedHilbert.projectiveSaturation J) (Saturation.GradedHilbert.projectiveSaturation_isSaturated J)).mpr
    (h.trans (Saturation.GradedHilbert.le_projectiveSaturation J))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.SaturationOrder.GradedHilbert
