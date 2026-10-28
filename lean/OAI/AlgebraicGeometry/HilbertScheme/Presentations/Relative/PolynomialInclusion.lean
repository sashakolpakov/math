import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialFamily
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientStructure

/-! # Polynomial Inclusion -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialInclusion.GradedHilbert

noncomputable section

/-! Every relative polynomial family has a canonical actual closed immersion
into the corresponding relative projective space. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

abbrev relativePolynomialAmbient {T : Over S} (x : T ⟶ M) : Scheme.{u} :=
  pullback (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) (x.left ≫ M.left.toSpecΓ)

def relativePolynomialInclusion {T : Over S} (x : T ⟶ M) :
    PolynomialFamily.GradedHilbert.relativePolynomialFamily M I x ⟶ relativePolynomialAmbient (n := n) M x := by
  let j : Proj (Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
  have hj : j ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) =
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I) := Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure I
  change pullback (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) (x.left ≫ M.left.toSpecΓ) ⟶
    pullback (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) (x.left ≫ M.left.toSpecΓ)
  exact pullback.lift (pullback.fst _ _ ≫ j) (pullback.snd _ _) (by
    rw [Category.assoc, hj]
    exact pullback.condition)

theorem relativePolynomialInclusion_fst {T : Over S} (x : T ⟶ M) :
    relativePolynomialInclusion M I x ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I := pullback.lift_fst _ _ _

theorem relativePolynomialInclusion_projection {T : Over S} (x : T ⟶ M) :
    relativePolynomialInclusion M I x ≫ pullback.snd _ _ =
      PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x := pullback.lift_snd _ _ _

theorem relativePolynomialInclusion_isPullback {T : Over S} (x : T ⟶ M) :
    IsPullback (relativePolynomialInclusion M I x) (pullback.fst _ _)
      (pullback.fst (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)) (x.left ≫ M.left.toSpecΓ))
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) := by
  let p := Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n)
  let pI := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  let b := x.left ≫ M.left.toSpecΓ
  let j : Proj (Graded.Quotient.GradedHilbert.quotientGrading I) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n) := Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I
  let k : pullback pI b ⟶ pullback p b := relativePolynomialInclusion M I x
  have hk₁ : k ≫ pullback.fst p b = pullback.fst pI b ≫ j := relativePolynomialInclusion_fst M I x
  have hk₂ : k ≫ pullback.snd p b = pullback.snd pI b := relativePolynomialInclusion_projection M I x
  have hj : j ≫ p = pI := Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure I
  change IsPullback k (pullback.fst pI b) (pullback.fst p b) j
  apply IsPullback.of_right _ hk₁ (IsPullback.of_hasPullback p b).flip
  rw [hk₂, hj]
  exact (IsPullback.of_hasPullback pI b).flip

instance relativePolynomialInclusion_isClosedImmersion {T : Over S} (x : T ⟶ M) :
    IsClosedImmersion (relativePolynomialInclusion M I x) :=
  MorphismProperty.of_isPullback (relativePolynomialInclusion_isPullback M I x).flip
    (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion_isClosedImmersion I)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialInclusion.GradedHilbert
