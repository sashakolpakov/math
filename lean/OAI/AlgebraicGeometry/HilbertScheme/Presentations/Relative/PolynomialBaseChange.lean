import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialInclusion

/-! # Polynomial Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialBaseChange.GradedHilbert

noncomputable section

/-! Actual cartesian base change of a relative polynomial family. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))

def relativePolynomialBaseMap {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    PolynomialFamily.GradedHilbert.relativePolynomialFamily M I (a ≫ x) ⟶ PolynomialFamily.GradedHilbert.relativePolynomialFamily M I x := by
  let p := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  let b := x.left ≫ M.left.toSpecΓ
  let b' := (a ≫ x).left ≫ M.left.toSpecΓ
  have hb : b' = a.left ≫ b := Category.assoc _ _ _
  change pullback p b' ⟶ pullback p b
  exact pullback.lift (pullback.fst p b') (pullback.snd p b' ≫ a.left) (by
    rw [Category.assoc, ← hb]
    exact pullback.condition)

theorem relativePolynomialBaseMap_fst {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    relativePolynomialBaseMap M I a x ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem relativePolynomialBaseMap_projection {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    relativePolynomialBaseMap M I a x ≫ PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x =
      PolynomialFamily.GradedHilbert.relativePolynomialProjection M I (a ≫ x) ≫ a.left := pullback.lift_snd _ _ _

theorem relativePolynomialBaseMap_isPullback {T U : Over S} (a : U ⟶ T) (x : T ⟶ M) :
    IsPullback (relativePolynomialBaseMap M I a x) (PolynomialFamily.GradedHilbert.relativePolynomialProjection M I (a ≫ x))
      (PolynomialFamily.GradedHilbert.relativePolynomialProjection M I x) a.left := by
  let p := Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  let b := x.left ≫ M.left.toSpecΓ
  let b' := (a ≫ x).left ≫ M.left.toSpecΓ
  have hb : b' = a.left ≫ b := Category.assoc _ _ _
  let k : pullback p b' ⟶ pullback p b := relativePolynomialBaseMap M I a x
  have hk₁ : k ≫ pullback.fst p b = pullback.fst p b' := relativePolynomialBaseMap_fst M I a x
  have hk₂ : k ≫ pullback.snd p b = pullback.snd p b' ≫ a.left :=
    relativePolynomialBaseMap_projection M I a x
  change IsPullback k (pullback.snd p b') (pullback.snd p b) a.left
  apply IsPullback.of_right _ hk₂ (IsPullback.of_hasPullback p b)
  rw [hk₁, ← hb]
  exact IsPullback.of_hasPullback p b'

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.PolynomialBaseChange.GradedHilbert
