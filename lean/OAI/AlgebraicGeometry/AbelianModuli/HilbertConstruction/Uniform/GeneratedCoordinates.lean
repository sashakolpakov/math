import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.DegreeGeneratedRelations
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Free.HomogeneousQuotients
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TruncationReconstruction
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration

/-! # Generated Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedCoordinates

noncomputable section

/-! Uniform Grassmannian coordinates for the single-degree truncation of a saturated flat projective family over a noetherian ring. -/

open _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert

universe u

def generatedHilbertRanks (n : ℕ) (P : Polynomial ℚ) (N d : ℕ) : ℕ :=
  if d < N then Fintype.card (Homogeneous.Coordinates.HomogeneousMonomials (Fin (n + 1)) d)
  else (P.eval (d : ℚ)).num.toNat

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
variable (N : ℕ) (hN : HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ N)

def uniformGeneratedQuotient (d : ℕ) :
    Module.Grassmannian R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d) (generatedHilbertRanks n P N d) where
  toSubmodule := Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) d
  finite_quotient := HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
  projective_quotient := by
    by_cases hd : d < N
    · rw [DegreeGeneratedRelations.degreeGeneratedIdeal_relations_below I N d hd]
      exact (Free.HomogeneousQuotients.freeHomogeneousQuotient R (Fin (n + 1)) d).projective_quotient
    · have he : Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) d =
          Homogeneous.IdealIncidence.homogeneousDegreeRelations I d :=
        HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert.uniformFamily_degreeGenerated_relations I hSat P hP N hN d (by omega)
      rw [he]
      exact (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformFlatFamilyHilbertGrassmannian I hSat P hP d (hN.trans (by omega))).projective_quotient
  rankAtStalk_eq p := by
    by_cases hd : d < N
    · rw [DegreeGeneratedRelations.degreeGeneratedIdeal_relations_below I N d hd, generatedHilbertRanks, ite_eq_left hd]
      exact (Free.HomogeneousQuotients.freeHomogeneousQuotient R (Fin (n + 1)) d).rankAtStalk_eq p
    · have he : Homogeneous.IdealIncidence.homogeneousDegreeRelations (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N) d =
          Homogeneous.IdealIncidence.homogeneousDegreeRelations I d :=
        HilbertScheme.Presentations.Uniform.FamilyGeneration.GradedHilbert.uniformFamily_degreeGenerated_relations I hSat P hP N hN d (by omega)
      rw [he, generatedHilbertRanks, ite_eq_right hd]
      exact HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree_rankAtStalk I hSat P hP d (hN.trans (by omega)) p

def uniformGeneratedData : GradedQuotientFamilies.GradedQuotientData R (Fin (n + 1)) (generatedHilbertRanks n P N) where
  quotient := uniformGeneratedQuotient I hSat P hP N hN
  variable_mul := Homogeneous.IdealIncidence.homogeneousDegreeRelations_multiply (HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N)

theorem uniformGeneratedData_ideal : (uniformGeneratedData I hSat P hP N hN).ideal =
    HilbertScheme.Presentations.DegreeGeneratedIdeal.GradedHilbert.degreeGeneratedIdeal I N := GradedIdealReconstruction.homogeneousIdealRelations_reconstruct _

theorem uniformGeneratedData_truncate_condition (B : ℕ) :
    ((uniformGeneratedData I hSat P hP N hN).truncate B).GeneratedFromDegree N :=
  ⟨fun d hd => DegreeGeneratedRelations.degreeGeneratedIdeal_relations_below I N d hd,
    fun d hd => DegreeGeneratedRelations.degreeGeneratedIdeal_relations_succ I N d hd⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.GeneratedCoordinates
