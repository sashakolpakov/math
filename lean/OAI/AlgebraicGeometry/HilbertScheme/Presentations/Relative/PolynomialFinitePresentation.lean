import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFamily
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Polynomial Finite Presentation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFinitePresentation.GradedHilbert

noncomputable section

/-! Over a locally noetherian parameter scheme, the proper polynomial family
is finitely presented, and this persists on arbitrary test schemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) [IsLocallyNoetherian M.left] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

instance relativePolynomialProjection_locallyOfFinitePresentation {T : Over S} (x : T ⟶ M) :
    LocallyOfFinitePresentation (PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x) := by
  let p := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  have : IsProper p := Projective.Properness.GradedHilbert.projectiveQuotient_proper I
  have : LocallyOfFinitePresentation (pullback.snd p M.left.toSpecΓ) := inferInstance
  let e := pullbackLeftPullbackSndIso p M.left.toSpecΓ x.left
  have hc : LocallyOfFinitePresentation
      (e.inv ≫ pullback.snd (pullback.snd p M.left.toSpecΓ) x.left) := inferInstance
  dsimp only [e] at hc
  rw [pullbackLeftPullbackSndIso_inv_snd_snd] at hc
  exact hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFinitePresentation.GradedHilbert
