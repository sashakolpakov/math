import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.QuotientTwistingFrames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.TwistingRestriction

/-! # Coefficient Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.CoefficientChange

noncomputable section

/-! The actual ambient projective O(1) commutes with every change of coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : CommRingCat.{u}} (φ : R ⟶ A) (n : ℕ)

def zeroQuotientCoefficientMorphism :
    Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n))) ⟶
      Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) :=
  (Projective.QuotientZero.projectiveQuotientZeroIso A n).hom.left ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫
    (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left

theorem zeroQuotientCoefficientMorphism_factor :
    zeroQuotientCoefficientMorphism φ n ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)) ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n := by
  have he : (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left ≫
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) = 𝟙 _ :=
    congrArg Over.Hom.left (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv_hom_id
  exact (Category.assoc _ _ _).trans
    (congrArg (fun z => (Projective.QuotientZero.projectiveQuotientZeroIso A n).hom.left ≫ z)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫ z) he).trans (Category.comp_id _))))

theorem zeroQuotientCoefficientMorphism_from_ambient :
    (Projective.QuotientZero.projectiveQuotientZeroIso A n).inv.left ≫ zeroQuotientCoefficientMorphism φ n =
      Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫ (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left := by
  have he : (Projective.QuotientZero.projectiveQuotientZeroIso A n).inv.left ≫ (Projective.QuotientZero.projectiveQuotientZeroIso A n).hom.left = 𝟙 _ :=
    congrArg Over.Hom.left (Projective.QuotientZero.projectiveQuotientZeroIso A n).inv_hom_id
  change (Projective.QuotientZero.projectiveQuotientZeroIso A n).inv.left ≫
    (Projective.QuotientZero.projectiveQuotientZeroIso A n).hom.left ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n ≫
      (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left = _
  rw [← Category.assoc, he, Category.id_comp]

def affineProjectiveTwistingBundle_coefficientIso :
    ((Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n).pullback (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n)).sheaf ≅
      (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle A n).sheaf := by
  let O := Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) 1
  let m := zeroQuotientCoefficientMorphism φ n
  let a := (Projective.QuotientZero.projectiveQuotientZeroIso A n).inv.left
  let e := Coefficient.QuotientTwistingFrames.coefficientQuotientTwistingBundleIso φ
    (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)) (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) m
      (zeroQuotientCoefficientMorphism_factor φ n)
  exact (Scheme.Modules.pullbackComp (Projective.CoefficientFunctoriality.polynomialProjectiveMap φ n) (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left).app
      O.sheaf ≪≫
    (Scheme.Modules.pullbackCongr (zeroQuotientCoefficientMorphism_from_ambient φ n).symm).app O.sheaf ≪≫
    (Scheme.Modules.pullbackComp a m).symm.app O.sheaf ≪≫ (Scheme.Modules.pullback a).mapIso e

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.CoefficientChange
