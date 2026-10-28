import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.RelationPresentation

/-! # Generators Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange.GradedHilbert

noncomputable section

/-! Degree quotients of finitely many homogeneous generators commute with arbitrary coefficient-ring extension. -/

open _root_.MvPolynomial TensorProduct

universe u v z

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
variable {n : ℕ} {ι : Type z}

theorem homogeneousGeneratorsIdeal_baseChange
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) :
    Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) =
      RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) N
        (fun i => (hg i).map (algebraMap R S)) := by
  apply HomogeneousIdeal.ext
  change Ideal.map (MvPolynomial.map (algebraMap R S)) (Ideal.span (Set.range g)) =
    Ideal.span (Set.range (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g))
  rw [Ideal.map_span, ← Set.range_comp]
  rfl

def homogeneousGeneratorsDegreeBaseChangeEquiv
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ) :
    S ⊗[R] Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal d ≃ₗ[S]
      Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) N
        (fun i => (hg i).map (algebraMap R S))).toIdeal d := by
  rw [← homogeneousGeneratorsIdeal_baseChange]
  exact Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := S) (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg) d

theorem homogeneousGeneratorsDegree_flat_baseChange
    (g : ι → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (N : ℕ) (hg : ∀ i, (g i).IsHomogeneous N) (d : ℕ)
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal g N hg).toIdeal d)] :
    Module.Flat S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (RelationPresentation.GradedHilbert.homogeneousGeneratorsIdeal (Finite.SyzygyLifting.GradedHilbert.mapRelationVector (algebraMap R S) g) N
      (fun i => (hg i).map (algebraMap R S))).toIdeal d) :=
  Module.Flat.of_linearEquiv (homogeneousGeneratorsDegreeBaseChangeEquiv (S := S) g N hg d).symm

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.GeneratorsBaseChange.GradedHilbert
