import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatnessLocal
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.QuotientFinitePresentation
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

/-! # Degree Flatness -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatness.GradedHilbert

noncomputable section

/-! A uniform finite-degree flatness test over arbitrary commutative coefficient rings. -/

open _root_.MvPolynomial TensorProduct

universe u z

variable {R : Type u} [CommRing R] {n : ℕ} {ι : Type z} [Fintype ι]

theorem homogeneous_quotients_flat_of_finite_flat_degrees
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hflat : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N)))
    (d : ℕ) : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)) := by
  let M := Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)
  apply Module.flat_of_localized_maximal
  intro P hP
  let A := Localization.AtPrime P
  let gA := SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R A) g
  have hgA (i : ι) : (gA i).IsHomogeneous N := (hg i).map (algebraMap R A)
  have hflatA : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat A (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal gA N hgA).toIdeal (e + N)) := by
    intro e he
    let := hflat e he
    exact Homogeneous.GeneratorsBaseChange.GradedHilbert.homogeneousGeneratorsDegree_flat_baseChange (S := A) g N hg (e + N)
  let := DegreeFlatnessLocal.GradedHilbert.homogeneous_quotients_free_of_finite_flat_degrees gA N hgA hflatA d
  let : Module.Flat A (A ⊗[R] M) := Module.Flat.of_linearEquiv
    (Homogeneous.GeneratorsBaseChange.GradedHilbert.homogeneousGeneratorsDegreeBaseChangeEquiv (S := A) g N hg (d + N))
  rw [← Module.flat_iff_of_isLocalization A P.primeCompl]
  exact Module.Flat.of_linearEquiv (LocalizedModule.equivTensorProduct P.primeCompl M)

theorem homogeneous_quotients_flat_finite_test_global
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    (∀ d, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N))) ↔
    (∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N))) := by
  constructor
  · exact fun h e _ => h e
  · exact homogeneous_quotients_flat_of_finite_flat_degrees g N hg

theorem homogeneous_quotients_projective_of_finite_flat_degrees
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hflat : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N)))
    (d : ℕ) : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N)) := by
  let := homogeneous_quotients_flat_of_finite_flat_degrees g N hg hflat d
  let := Homogeneous.QuotientFinitePresentation.GradedHilbert.homogeneousGeneratorsDegree_finitePresentation g N hg d
  exact Module.Flat.projective_of_finitePresentation
    (R := R) (M := Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (d + N))

theorem projectiveQuotient_flat_of_finite_degree_test
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N)
    (hflat : ∀ e ≤ Coordinate.SyzygyBound.GradedHilbert.homogeneousSyzygyDegreeBound n (Fintype.card ι) N,
      Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal (e + N))) :
    AlgebraicGeometry.Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg))) := by
  apply Presentations.Projective.Flatness.GradedHilbert.projectiveQuotient_flat_of_eventually_flat (Homogeneous.RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) N
  intro d hd
  have he : d - N + N = d := Nat.sub_add_cancel hd
  rw [← he]
  exact homogeneous_quotients_flat_of_finite_flat_degrees g N hg hflat (d - N)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.DegreeFlatness.GradedHilbert
