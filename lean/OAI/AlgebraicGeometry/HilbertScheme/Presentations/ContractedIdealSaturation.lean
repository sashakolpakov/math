import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedHomogeneousQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Localization

/-! # Contracted Ideal Saturation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealSaturation.GradedHilbert

noncomputable section

/-! Coefficient contraction preserves homogeneous saturation. -/

open _root_.MvPolynomial

universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Algebra R A] {n : ℕ}

theorem contractedHomogeneousIdeal_saturated (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading A n))
    (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) : Hilbert.Polynomial.GradedHilbert.IsSaturated (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I).toIdeal := by
  intro f d hf h
  obtain ⟨m, hm⟩ := h
  change MvPolynomial.map (algebraMap R A) f ∈ I.toIdeal
  apply hI.mem_of_variable_powers _ d (hf.map (algebraMap R A))
  intro i
  have hXi : (X (R := R) i ^ m).IsHomogeneous m := by
    simpa only [one_mul] using (isHomogeneous_X R i).pow m
  have hi := hm (X i ^ m) hXi
  refine ⟨m, ?_⟩
  change MvPolynomial.map (algebraMap R A) (X i ^ m * f) ∈ I.toIdeal at hi
  simpa only [map_mul, map_pow, MvPolynomial.map_X] using hi

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.ContractedIdealSaturation.GradedHilbert
