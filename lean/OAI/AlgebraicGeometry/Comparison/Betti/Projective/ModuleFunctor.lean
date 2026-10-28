import OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleCechAcyclicity
import OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCoverNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechNaturality
import OAI.AlgebraicGeometry.Comparison.Betti.ProjectiveTwist.ReferenceCechMap

/-! # Module Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleFunctor.Dolbeault

noncomputable section

/-! The original projective comparison is a natural transformation on all algebraic modules. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

open OAI.AlgebraicGeometry.Comparison.Betti.Module.AnalytificationCechNaturality OAI.AlgebraicGeometry.Comparison.Betti.AdditiveCoverNaturality.Cech

attribute [local instance] IntersectionHolomorphy.Dolbeault.projectiveIntegral IntersectionHolomorphy.Dolbeault.projectiveSmooth IntersectionHolomorphy.Dolbeault.projectiveNativeChartedSpace

def projectiveAlgebraicModuleCechFunctor (n : ℕ) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  SheafOfModules.toSheaf.{0} (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).ringCatSheaf ⋙
    SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n)

def projectiveAnalyticModuleCechFunctor (n : ℕ) :
    (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules ⥤ CochainComplex AddCommGrpCat.{0} ℕ :=
  ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n ⋙ SheafCohomology.Cech.InjectiveBicomplex.TopCat.Sheaf.cechSheafComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)

def projectiveModuleOriginalCechMap (n : ℕ) (M : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules) :
    (projectiveAlgebraicModuleCechFunctor n).obj M ⟶ (projectiveAnalyticModuleCechFunctor n).obj M :=
  Module.AnalytificationCechMap.moduleAnalytificationCechMap (Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)) M (Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n) ≫
    (AdditiveCechCoverCongr.additiveCechCoverCongrIso ((ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).obj M).obj
      (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n)).hom

theorem projectiveModuleOriginalCechMap_naturality (n : ℕ)
    {M N : (Foundations.Scheme.ProjectiveSpace.projectiveSpace n).Modules} (g : M ⟶ N) :
    (projectiveAlgebraicModuleCechFunctor n).map g ≫ projectiveModuleOriginalCechMap n N =
      projectiveModuleOriginalCechMap n M ≫ (projectiveAnalyticModuleCechFunctor n).map g := by
  let X := Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase n)
  let U := Foundations.Scheme.ProjectiveCoordinateCover.projectiveCoordinateOpen n
  let A := cechComplexFunctor (A := AddCommGrpCat.{0}) (fun i => Open.AffineIsoEvaluation.analyticOpen X (U i))
  let uM := Module.AnalytificationCechMap.moduleAnalytificationCechMap X M U
  let uN := Module.AnalytificationCechMap.moduleAnalytificationCechMap X N U
  let eM := (AdditiveCechCoverCongr.additiveCechCoverCongrIso ((ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).obj M).obj
    (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n)).hom
  let eN := (AdditiveCechCoverCongr.additiveCechCoverCongrIso ((ModuleCechAcyclicity.Dolbeault.projectiveAnalytifiedAdditiveFunctor n).obj N).obj
    (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n)).hom
  let q := Module.AnalytificationUnitNaturality.analytifiedModuleAdditivePresheafMap X g
  have h₁ := Module.AnalytificationCechNaturality.moduleAnalytificationCechMap_naturality X U g
  have h₂ := AdditiveCoverNaturality.Cech.additiveCechCoverCongrIso_naturality q (ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveAnalyticCoverEq n)
  change (cechComplexFunctor U).map (Module.AnalytificationUnitNaturality.moduleAdditivePresheafMap X g) ≫ (uN ≫ eN) =
    (uM ≫ eM) ≫ (cechComplexFunctor (Intersections.Dolbeault.projectiveStandardCover n)).map q
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ eN) h₁.symm).trans ((Category.assoc uM (A.map q) eN).trans
      ((congrArg (uM ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

def projectiveModuleCechComparison (n : ℕ) :
    projectiveAlgebraicModuleCechFunctor n ⟶ projectiveAnalyticModuleCechFunctor n where
  app M := projectiveModuleOriginalCechMap n M
  naturality {M N} g := projectiveModuleOriginalCechMap_naturality n (M := M) (N := N) g

theorem projectiveModuleOriginalCechMap_twist (n : ℕ) (j : Fin (n + 1)) (d : ℤ) :
    projectiveModuleOriginalCechMap n (SheafCohomology.Projective.TwistPowers.MvPolynomial.coordinateHyperplaneTwist (R := ℂ) j d) =
      ProjectiveTwist.ReferenceCechMap.Dolbeault.projectiveTwistOriginalCechMap n j d := rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.Projective.ModuleFunctor.Dolbeault
