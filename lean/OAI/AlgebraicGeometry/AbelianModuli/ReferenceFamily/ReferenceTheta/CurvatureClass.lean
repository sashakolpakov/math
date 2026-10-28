import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.ConnectionCech
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReferenceTheta.LogarithmicDefect
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureDefect

/-! # Curvature Class -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! The normalized original curvature and the original rational Chern
defect have the same class in the genuine Cech-de Rham total complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] {s : ℕ} {P : Datum.RankThreePELDatum E s}
    {z : P.domain} {F : Reference.Fiber.ReferenceAnalyticFiber P z} {hP : P.IsAdmissible}
    (M : Reference.AlgebraicModel.ReferenceAlgebraicModel F hP) (U V : RepresentationTheory.Theta.Geometric.AutomorphicFamilies.CM.Torus.AutomorphicTheta.Family (F.polarizationFactor hP))
    (f : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase U.projectiveDimension))
    (g : M.abelian.toOver ⟶ Over.mk (Foundations.Scheme.ProjectiveSpace.projectiveSpaceToBase V.projectiveDimension))
    (hf : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map f (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint U.projectiveDimension (U.projectiveMap t))
    (hg : ∀ t, ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map g (M.period t) =
      ComplexPoints.Analytic.ProjectiveScheme.projectivizationSchemePoint V.projectiveDimension (V.projectiveMap t))

local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCurvatureClass_integral : IsIntegral M.abelian.toOver.left := M.abelian.variety.property
local instance Reference.AlgebraicModel.ReferenceAlgebraicModel.thetaCurvatureClass_smooth : Smooth M.abelian.toOver.hom := M.abelian.variety.presentation.smooth
attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeReferenceCurvature_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d M.nativeReferenceCurvature = 0 := by
  let hp : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm F.periodData.space F.periodData.periodTorus 3 →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 3 :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.pullback M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff)
  have hd : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d M.nativeReferenceCurvature = hp (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d F.referenceTorusCurvature) :=
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d_pullback M.period.symm (Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex M.period.symm.contMDiff)
      F.referenceTorusCurvature
  exact hd.trans ((congrArg hp F.referenceTorusCurvature_closed).trans hp.map_zero)

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaNormalizedCurvature_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d M.nativeThetaNormalizedCurvature = 0 := by
  exact (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d.map_smul (-ReferenceTheta.ConnectionCech.chernLogScale) M.nativeReferenceCurvature).trans
    ((congrArg (fun b : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver) 3 => -ReferenceTheta.ConnectionCech.chernLogScale • b) M.nativeReferenceCurvature_closed).trans
        (smul_zero _))

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaCurvatureCocycle :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex (RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver)) 2 :=
  ⟨M.nativeThetaNormalizedCurvature, (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff _ 2 _).mpr M.nativeThetaNormalizedCurvature_closed⟩

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaCurvatureTotalCocycle :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)) 2 :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
    (M.thetaChernCover U V f g hf hg)) 2 M.nativeThetaCurvatureCocycle

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaRationalDefectTotal :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)).X 2 :=
  Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (M.thetaChernCover U V f g hf hg) 2 0 2 rfl
    (ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect.CM.Construction.rationalCechManifoldForm (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg) 2
      (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints M.abelian.toOver))
        (M.thetaChernCover U V f g hf hg) (M.thetaChernLogCech U V f g hf hg)
        (M.thetaChernLogCech_cocycle U V f g hf hg)))

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeTheta_curvature_rational_defect_boundary (hdeg : V.degree = U.degree + 1) :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)).d 1 2
      (ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (M.thetaChernCover U V f g hf hg)
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) (M.nativeThetaLogarithmCech U V f g hf hg)) =
      (M.nativeThetaCurvatureTotalCocycle U V f g hf hg).val - M.nativeThetaRationalDefectTotal U V f g hf hg := by
  refine (M.nativeTheta_curvature_logarithmic_boundary U V f g hf hg hdeg).trans ?_
  exact congrArg (fun b : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian)
      (M.thetaChernCover U V f g hf hg) 0 2 =>
    (M.nativeThetaCurvatureTotalCocycle U V f g hf hg).val -
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (M.thetaChernCover U V f g hf hg) 2 0 2 rfl b)
    (M.nativeThetaLogarithmCech_delta U V f g hf hg)

def Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeThetaRationalDefectCocycle (hdeg : V.degree = U.degree + 1) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)) 2 :=
  ⟨M.nativeThetaRationalDefectTotal U V f g hf hg,
    ComplexMultiplication.HodgeComparison.ProjectiveCurvatureDefect.CM.Construction.cochain_closed_of_difference_boundary _ (M.nativeThetaCurvatureTotalCocycle U V f g hf hg)
      (ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (M.thetaChernCover U V f g hf hg)
        (M.nativeThetaConnectionCech U V f g hf hg hdeg) (M.nativeThetaLogarithmCech U V f g hf hg)) _
      (M.nativeTheta_curvature_rational_defect_boundary U V f g hf hg hdeg)⟩

theorem Reference.AlgebraicModel.ReferenceAlgebraicModel.nativeTheta_curvature_total_class (hdeg : V.degree = U.degree + 1) :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)) 2
      (M.nativeThetaCurvatureTotalCocycle U V f g hf hg) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := RepresentationTheory.Theta.Geometric.AlgebraicAction.AbelianModel M.abelian) (M.thetaChernCover U V f g hf hg)) 2
      (M.nativeThetaRationalDefectCocycle U V f g hf hg hdeg) := by
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ _ 1 _ _).mpr
  exact ⟨ComplexMultiplication.HodgeComparison.ConnectionTransgression.CM.Construction.connectionTotalPrimitive (M.thetaChernCover U V f g hf hg)
    (M.nativeThetaConnectionCech U V f g hf hg hdeg) (M.nativeThetaLogarithmCech U V f g hf hg),
      M.nativeTheta_curvature_rational_defect_boundary U V f g hf hg hdeg⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
