import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.PolynomialInclusion

/-! # Projective Point -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectivePoint.GradedHilbert

noncomputable section

/-! Actual polynomial projective fibers of the original-base relative
projective space, for every ring-valued parameter point. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {S : Scheme.{u}} (M : Over S) (n : ℕ)
variable {R : Type u} [CommRing R] (a : Spec (CommRingCat.of R) ⟶ M.left)

def polynomialPointMorphismOver (f : Spec (CommRingCat.of R) ⟶ S) (ha : a ≫ M.hom = f) : Over.mk f ⟶ M :=
  Over.homMk a ha

def globalProjectiveSchemePointMap : Proj (Hilbert.Polynomial.GradedHilbert.grading R n) ⟶ (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left :=
  Projective.Point.GradedHilbert.projectiveSchemePointMap n a ≫ Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap M.hom n

theorem globalProjectiveSchemePointMap_isPullback :
    IsPullback (globalProjectiveSchemePointMap M n a) (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))
      (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).hom (a ≫ M.hom) :=
  (Projective.Point.GradedHilbert.projectiveSchemePointMap_isPullback n a).paste_horiz (Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap_isPullback M.hom n)

def globalPolynomialPointPresentation
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
    (f : Spec (CommRingCat.of R) ⟶ S) (ha : a ≫ M.hom = f) :
    Projective.Quotient.GradedHilbert.projectiveQuotient (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≅
      Relative.PolynomialFamily.GradedHilbert.relativePolynomialFamily M I (polynomialPointMorphismOver M a f ha) := Projective.QuotientPoint.GradedHilbert.projectiveQuotientPointIso M I a

theorem projectiveQuotientPointIso_global_projective
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading Γ(M.left, ⊤) n))
    (f : Spec (CommRingCat.of R) ⟶ S) (ha : a ≫ M.hom = f) :
    (globalPolynomialPointPresentation M n a I f ha).hom ≫ PolynomialInclusion.GradedHilbert.globalPolynomialInclusion M I (polynomialPointMorphismOver M a f ha) ≫
        (prod.snd : Over.mk f ⨯ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n ⟶ Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n).left =
      Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Projective.QuotientPoint.GradedHilbert.pointHomogeneousIdeal M I a) ≫ globalProjectiveSchemePointMap M n a := by
  rw [PolynomialInclusion.GradedHilbert.globalPolynomialInclusion_projective]
  have h := congrArg (fun f => f ≫ Relative.ProjectiveBaseChange.GradedHilbert.relativeProjectiveBaseMap M.hom n)
    (Intrinsic.PolynomialPointComparison.GradedHilbert.projectiveQuotientPointIso_native_inclusion M I a)
  exact (Category.assoc _ _ _).symm.trans
    (h.trans (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Global.ProjectivePoint.GradedHilbert
