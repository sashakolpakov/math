import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialLocus
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatFiberPolynomialSpecialization

/-! # Flat Hilbert Polynomial Partition -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialPartition.PolarizationEmbedding

noncomputable section

/-! A flat noetherian projective family has a finite, locally constant
actual fiber-polynomial function. Its open-and-closed pieces also detect
all coefficient-field specializations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def residueHilbertPolynomial (p : PrimeSpectrum R) : Polynomial ℚ :=
  (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).choose

theorem residueHilbertPolynomial_spec (p : PrimeSpectrum R) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal
      (residueHilbertPolynomial I p) :=
  (HilbertScheme.Presentations.Hilbert.Existence.GradedHilbert.exists_hilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).choose_spec

theorem residueHilbertPolynomial_eq_iff (p : PrimeSpectrum R) (P : Polynomial ℚ) :
    residueHilbertPolynomial I p = P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal P := by
  constructor
  · intro h
    exact h ▸ residueHilbertPolynomial_spec I p
  · exact HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertPolynomial_unique (residueHilbertPolynomial_spec I p)

variable [IsNoetherianRing R] [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem residueHilbertPolynomial_isLocallyConstant : IsLocallyConstant (residueHilbertPolynomial I) := by
  apply IsLocallyConstant.iff_isOpen_fiber.mpr
  intro P
  have h : (residueHilbertPolynomial I) ⁻¹' {P} =
      {p : PrimeSpectrum R | HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal P} := by
    ext p
    exact residueHilbertPolynomial_eq_iff I p P
  rw [h]
  exact (FlatHilbertPolynomialLocus.PolarizationEmbedding.isClopen_residue_hilbertPolynomial I P).isOpen

def residueHilbertPolynomialOpen (P : Polynomial ℚ) : (Spec (.of R)).Opens :=
  ⟨{p | residueHilbertPolynomial I p = P},
    (residueHilbertPolynomial_isLocallyConstant I).isOpen_fiber P⟩

theorem residueHilbertPolynomialOpen_isClopen (P : Polynomial ℚ) :
    IsClopen (residueHilbertPolynomialOpen I P : Set (Spec (.of R))) :=
  (residueHilbertPolynomial_isLocallyConstant I).isClopen_fiber P

theorem residueHilbertPolynomial_finite_range : Set.Finite (Set.range (residueHilbertPolynomial I)) :=
  (residueHilbertPolynomial_isLocallyConstant I).range_finite

theorem exists_finite_residueHilbertPolynomial_cover :
    ∃ F : Finset (Polynomial ℚ), ∀ p : Spec (.of R),
      ∃ P ∈ F, p ∈ residueHilbertPolynomialOpen I P := by
  classical
  refine ⟨(residueHilbertPolynomial_finite_range I).toFinset, fun p => ?_⟩
  exact ⟨residueHilbertPolynomial I p,
    (residueHilbertPolynomial_finite_range I).mem_toFinset.mpr ⟨p, rfl⟩, rfl⟩

theorem saturated_field_polynomial_iff_mem_open
    {K : Type u} [Field K] (φ : R →+* K) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).toIdeal P ↔
      (IsLocalRing.closedPoint K).comap φ ∈ residueHilbertPolynomialOpen I P :=
  (FlatFiberPolynomialSpecialization.PolarizationEmbedding.saturated_field_hilbertPolynomial_iff_residue I φ P).trans
    (residueHilbertPolynomial_eq_iff I _ P).symm

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatHilbertPolynomialPartition.PolarizationEmbedding
