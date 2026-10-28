import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HypercohomologyForget
import OAI.AlgebraicGeometry.Comparison.Betti.Affine.ExteriorAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.Complex.Extension

/-! # Additive Complex Extension -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AdditiveComplexExtension

noncomputable section

/-! The preserved additive algebraic complex is the extension of its actual nonnegative terms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

def algebraicAdditiveSheafComplex : CochainComplex (HypercohomologyForget.AdditiveZariskiSheaves X) ℕ :=
  ((ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive (TopCat.of X.left)).mapHomologicalComplex (.up ℕ)).obj
    (Sheaves.algebraicDeRhamSheafComplex X)

def algebraicAdditiveComplexExtensionIso :
    HypercohomologyForget.algebraicAdditiveSheafComplexInt X ≅
      (algebraicAdditiveSheafComplex X).extend (ComplexShape.embeddingUpIntGE 0) := by
  let F : Sheaves.ComplexSheaves X ⥤ HypercohomologyForget.AdditiveZariskiSheaves X :=
    ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive (TopCat.of X.left)
  have : F.Additive := inferInstanceAs
    (ComplexHypercohomologyForget.Coefficients.forgetComplexAdditive (TopCat.of X.left)).Additive
  exact (F.mapHomologicalComplex (.up ℤ)).mapIso (Analytic.De.algebraicSheafIntExtensionIso X) ≪≫
    Complex.Extension.mapExtendIso F (ComplexShape.embeddingUpIntGE 0)
      (Sheaves.algebraicDeRhamSheafComplex X)

theorem algebraicAdditiveSheafComplex_X (n : ℕ) :
    (algebraicAdditiveSheafComplex X).X n = Affine.ExteriorAcyclicity.algebraicFormAdditiveSheaf X n := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.AdditiveComplexExtension
