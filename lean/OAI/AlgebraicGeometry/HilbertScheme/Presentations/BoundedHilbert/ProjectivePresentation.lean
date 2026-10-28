import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.Proper
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoordinateProjectivePresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.DegreeIndexNonempty

/-! # Projective Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ProjectivePresentation.GradedHilbert

noncomputable section

/-! The bounded Hilbert parameter scheme has the exact projective
presentation required by the Presentations statement, under its polynomial rank profile. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.CoordinateProjectivePresentation.PolynomialProjective

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] {n N : ℕ}
variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable (P : Polynomial ℚ)
variable (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P) P)
variable (hN : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ N)
variable (hr : Fintype.card ι = (P.eval (N : ℚ)).num.toNat)

def boundedHilbertProjectivePresentation : Has.Core.ProjectivePresentation
    (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) := by
  apply Classical.choice
  obtain ⟨e, he, hb⟩ := Proper.GradedHilbert.boundedHilbert_projective_embedding (S := S) P hP hN hr
  let := he
  exact ⟨Finite.CoordinateProjectivePresentation.PolynomialProjective.projectivePresentationOfFiniteCoordinates _ e hb⟩

include hP hN hr in
theorem boundedHilbert_isProjectiveOver : Has.Core.IsProjectiveOver
    (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S (Presentations.Polynomial.DegreeRankProfile.GradedHilbert.polynomialDegreeRankProfile.{u} n N P)) :=
  ⟨boundedHilbertProjectivePresentation P hP hN hr⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.ProjectivePresentation.GradedHilbert
