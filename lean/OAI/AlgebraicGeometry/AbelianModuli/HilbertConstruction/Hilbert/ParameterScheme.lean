import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Generated.ParameterQuasiProjectivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyProjectiveParameters
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmptyProjectiveFamilies

/-! # Parameter Scheme -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterScheme

noncomputable section

/-! A specified quasi-projective Hilbert parameter scheme and actual universal projective family over every base. Bounds and the empty numerical case are part of the construction. Universality beyond locally noetherian tests is not asserted here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

def hilbertParameterTruncation (n : ℕ) (P : Polynomial ℚ) : ℕ :=
  max (Truncated.FinitePersistence.truncatedFlatnessBound n (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P))
    (Truncated.PolynomialTest.truncatedHilbertTestBound n (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P))

theorem hilbertParameterTruncation_flat (n : ℕ) (P : Polynomial ℚ) :
    Truncated.FinitePersistence.truncatedFlatnessBound n (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P) ≤ hilbertParameterTruncation.{u} n P :=
  Nat.le_max_left _ _

theorem hilbertParameterTruncation_test (n : ℕ) (P : Polynomial ℚ) :
    Truncated.PolynomialTest.truncatedHilbertTestBound n (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P) ≤ hilbertParameterTruncation.{u} n P :=
  Nat.le_max_right _ _

theorem hilbertParameterTruncation_degree (n : ℕ) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ hilbertParameterTruncation.{u} n P :=
  (Nat.le_add_right _ _).trans (hilbertParameterTruncation_flat n P)

def hilbertParameterScheme (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) : Over S := by
  classical
  exact if Generated.RankTests.GeneratedHilbertRankTest n P (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P) then
    Truncated.GeneratedParameters.truncatedGeneratedParameters S n (hilbertParameterTruncation.{u} n P)
      (Uniform.GeneratedCoordinates.generatedHilbertRanks n P (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P)) (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P)
  else EmptyProjectiveParameters.emptyProjectiveParameter S

def hilbertParameterQuasiProjectivePresentation (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    Projective.ProjectivePresentations.QuasiProjectivePresentation (hilbertParameterScheme S n P) := by
  classical
  unfold hilbertParameterScheme
  split_ifs
  · exact Generated.ParameterQuasiProjectivity.truncatedGeneratedQuasiProjectivePresentation S n (hilbertParameterTruncation.{u} n P)
      (Uniform.GeneratedCoordinates.generatedHilbertRanks n P (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P)) (HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P)
      (hilbertParameterTruncation_degree n P)
  · exact (EmptyProjectiveParameters.emptyParameterProjectivePresentation S).quasiProjective

def hilbertUniversalFamily (S : Scheme.{u}) (n : ℕ) (P : Polynomial ℚ) :
    RelativeProjective.Families.RelativeProjectiveHilbertFamily (hilbertParameterScheme S n P).left n P := by
  classical
  unfold hilbertParameterScheme
  split_ifs with h
  · exact Generated.ParameterFamilies.generatedParameterHilbertFamily (𝟙 _)
      (hilbertParameterTruncation_flat n P) (hilbertParameterTruncation_test n P) h
  · exact EmptyProjectiveFamilies.emptyRelativeProjectiveHilbertFamily n P

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Hilbert.ParameterScheme
