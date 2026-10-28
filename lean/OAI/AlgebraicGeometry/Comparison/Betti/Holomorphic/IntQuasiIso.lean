import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.Int
import OAI.AlgebraicGeometry.Comparison.Betti.Analytic.De
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafQuasiIso
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-! # Int Quasi Iso -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntQuasiIso

noncomputable section

/-! The actual integer-indexed holomorphic comparison is invertible in the derived category. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomologicalComplex

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

theorem holomorphicSmoothSheafMapInt_quasiIso : QuasiIso (Int.holomorphicSmoothSheafMapInt X) := by
  apply (quasiIso_extendMap_iff _ (ComplexShape.embeddingUpIntGE 0)).mpr
  exact SheafQuasiIso.inclusionSheafMap_quasiIso (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def derivedHolomorphicSmoothIso :
    DerivedCategory.Q.obj (Int.analyticHolomorphicSheafComplexInt X) ≅
      DerivedCategory.Q.obj (Analytic.De.analyticDeRhamSheafComplexInt X) := by
  let Q : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℤ ⥤ DerivedCategory (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) :=
    DerivedCategory.Q
  have h : IsIso (Q.map (Int.holomorphicSmoothSheafMapInt X)) :=
    Localization.inverts Q (HomologicalComplex.quasiIso (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) (.up ℤ))
      (Int.holomorphicSmoothSheafMapInt X) (holomorphicSmoothSheafMapInt_quasiIso X)
  exact asIso (Q.map (Int.holomorphicSmoothSheafMapInt X))

theorem derivedHolomorphicSmoothIso_factorization :
    DerivedCategory.Q.map (Int.algebraicToHolomorphicSheafMapInt X) ≫
      (derivedHolomorphicSmoothIso X).hom = DerivedCategory.Q.map (Analytic.De.algebraicToAnalyticSheafMapInt X) := by
  change DerivedCategory.Q.map (Int.algebraicToHolomorphicSheafMapInt X) ≫
    DerivedCategory.Q.map (Int.holomorphicSmoothSheafMapInt X) = _
  rw [← Functor.map_comp, Int.algebraicToHolomorphicSheafMapInt_factorization]

end

end OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.IntQuasiIso
