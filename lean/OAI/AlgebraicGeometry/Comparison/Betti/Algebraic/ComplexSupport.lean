import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De
import Mathlib.Algebra.Homology.CochainComplexPlus

/-! # Complex Support -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ComplexSupport

noncomputable section

/-! The preserved algebraic de Rham complex has its actual nonnegative support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase)

instance algebraicDeRhamSheafComplexInt_nonnegative :
    (Sheaves.algebraicDeRhamSheafComplexInt X).IsStrictlyGE 0 :=
  CochainComplex.isStrictlyGE_of_iso (Analytic.De.algebraicSheafIntExtensionIso X).symm 0

def algebraicDeRhamSheafComplexPlus : CochainComplex.Plus (Sheaves.ComplexSheaves X) :=
  ⟨Sheaves.algebraicDeRhamSheafComplexInt X, 0, algebraicDeRhamSheafComplexInt_nonnegative X⟩

theorem algebraicDeRhamSheafComplexInt_negative (n : ℤ) (hn : n < 0) :
    Limits.IsZero ((Sheaves.algebraicDeRhamSheafComplexInt X).X n) :=
  (Sheaves.algebraicDeRhamSheafComplexInt X).isZero_of_isStrictlyGE 0 n hn

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.ComplexSupport
