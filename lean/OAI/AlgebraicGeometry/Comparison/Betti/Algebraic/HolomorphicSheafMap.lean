import OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicPresheaf
import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.SheafComplex

/-! # Holomorphic Sheaf Map -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicSheafMap

noncomputable section

/-! The actual algebraic realization descends to the analytic holomorphic sheaf complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable (X : Over Foundations.Scheme.ProjectiveSpace.complexBase) [IsIntegral X.left] [Smooth X.hom]

def analyticHolomorphicSheafComplex : CochainComplex (Betti.Smooth.SheafMap.AnalyticComplexSheaves X) ℕ :=
  Holomorphic.SheafComplex.sheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)

def zariskiHolomorphicSheafComplex : CochainComplex (Sheaves.ComplexSheaves X) ℕ :=
  ((Betti.Smooth.SheafMap.analytificationPushforward X).mapHomologicalComplex (.up ℕ)).obj (analyticHolomorphicSheafComplex X)

def zariskiHolomorphicSheafUnit : HolomorphicPresheaf.zariskiHolomorphicPresheafComplex X ⟶
    ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
      (.up ℕ)).obj (zariskiHolomorphicSheafComplex X) :=
  ((Cech.PushforwardFunctor.presheafDirectImage (Analytification.Base.analytificationMap X)).mapHomologicalComplex (.up ℕ)).map
    ((Holomorphic.SheafComplex.complexSheafificationAdjunction (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)).unit.app
      (Holomorphic.Presheaf.presheafComplex (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)))

def algebraicToHolomorphicSheafMap : Sheaves.algebraicDeRhamSheafComplex X ⟶ zariskiHolomorphicSheafComplex X :=
  ((Sheaf.CochainPullback.sheafificationComplexAdjunction X).homEquiv (Sheaves.deRhamPresheafComplex X)
    (zariskiHolomorphicSheafComplex X)).symm
      (HolomorphicPresheaf.presheafHolomorphicCochainMap X ≫ zariskiHolomorphicSheafUnit X)

theorem algebraicToHolomorphicSheafMap_normalization :
    (Sheaf.CochainPullback.sheafificationComplexAdjunction X).unit.app (Sheaves.deRhamPresheafComplex X) ≫
        ((sheafToPresheaf (Opens.grothendieckTopology X.left) (ModuleCat.{0} ℂ)).mapHomologicalComplex
          (.up ℕ)).map (algebraicToHolomorphicSheafMap X) =
      HolomorphicPresheaf.presheafHolomorphicCochainMap X ≫ zariskiHolomorphicSheafUnit X :=
  (Sheaf.CochainPullback.sheafificationComplexAdjunction X).homEquiv (Sheaves.deRhamPresheafComplex X)
    (zariskiHolomorphicSheafComplex X) |>.apply_symm_apply _

def zariskiHolomorphicSmoothSheafMap : zariskiHolomorphicSheafComplex X ⟶ Betti.Smooth.SheafMap.zariskiSmoothSheafComplex X :=
  ((Betti.Smooth.SheafMap.analytificationPushforward X).mapHomologicalComplex (.up ℕ)).map
    (Holomorphic.SheafComplex.inclusionSheafMap (RegularSmoothness.NativeModel X) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Algebraic.HolomorphicSheafMap
