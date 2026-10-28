import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.PolynomialSubfunctor
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.UniversalPolynomial

/-! # Polynomial Transformation -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PolynomialTransformation.GradedHilbert

noncomputable section

/-! The constructed bounded Hilbert universal family defines a natural
map into the exact native polynomial Hilbert subfunctor on every test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {ι : Type u} [Fintype ι] [DecidableEq ι] (n N : ℕ)
variable (S : Scheme.{u}) [IsLocallyNoetherian S] (q : ℕ → ℕ) (P : Polynomial ℚ)
variable (hP : DegreeLocus.GradedHilbert.RankProfileRealizes.{u} n N q P)

def boundedHilbertPolynomialTransformation : yoneda.obj (Data.GradedHilbert.boundedHilbertOver (ι := ι) n N S q) ⟶
    (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) P).toFunctor where
  app T := ↾fun x => ⟨Hilbert.Functor.pullbackFamily (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) x
    (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily (ι := ι) n N S q),
    FiberPolynomialBaseChange.Core.hasFiberHilbertPolynomial_pullback (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) x
      (UniversalFamily.GradedHilbert.boundedHilbertUniversalFamily n N S q) P (UniversalPolynomial.GradedHilbert.boundedHilbertUniversalFamily_hasFiberHilbertPolynomial n N S q P hP)⟩
  naturality T U f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact Hilbert.Functor.pullbackFamily_comp (Intrinsic.PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) f.unop x _

theorem boundedHilbertPolynomialTransformation_inclusion :
    boundedHilbertPolynomialTransformation (ι := ι) n N S q P hP ≫
      (Hilbert.PolynomialSubfunctor.Core.hilbertPolynomialSubfunctor (Intrinsic.ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n) P).ι =
        UniversalFamily.GradedHilbert.boundedHilbertUniversalTransformation (ι := ι) n N S q := rfl

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.BoundedHilbert.PolynomialTransformation.GradedHilbert
