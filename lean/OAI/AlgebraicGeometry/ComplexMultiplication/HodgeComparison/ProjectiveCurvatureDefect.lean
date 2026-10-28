import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveConnectionCech
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectivePhaseDefect

/-! # Projective Curvature Defect -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureDefect.CM.Construction

noncomputable section

/-! The curvature and the actual rational logarithmic defect have
the same class in the genuine Čech–de Rham total complex. -/

open _root_.CategoryTheory _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

theorem cochain_closed_of_difference_boundary
    (K : CochainComplex (ModuleCat.{0} ℂ) ℕ) (u : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K 2)
    (t : K.X 1) (v : K.X 2) (h : K.d 1 2 t = u.val - v) :
    v ∈ AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles K 2 := by
  rw [AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff]
  have hu := (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff K 2 u.val).mp u.property
  have ht : K.d 2 3 (K.d 1 2 t) = 0 :=
    ConcreteCategory.congr_hom (K.d_comp_d 1 2 3) t
  have hv : 0 = -(K.d 2 3 v) := by
    calc
      0 = K.d 2 3 (K.d 1 2 t) := ht.symm
      _ = K.d 2 3 (u.val - v) := congrArg (K.d 2 3) h
      _ = -(K.d 2 3 v) := by rw [map_sub, hu, zero_sub]
  exact neg_eq_zero.mp hv.symm

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [NormalSpace M]
  {ι : Type} [Fintype ι]
  (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def projectiveCurvatureCocycle : AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 :=
  ⟨ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol, by
    apply (AlgebraicTopology.Cohomology.Singular.Representatives.mem_cochainCocycles_iff (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamComplex E M) 2 (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol)).mpr
    change Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol) = 0
    exact ProjectiveGluing.CM.Construction.projectiveCurvatureForm_closed p hp hhol⟩

def projectiveCurvatureTotalCocycle :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2 :=
  AlgebraicTopology.Cohomology.Singular.RepresentativesNaturality.cochainCocycleMap (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2
    (projectiveCurvatureCocycle p hp hhol)

def projectiveRationalDefectTotal :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)).X 2 :=
  Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2 0 2 rfl
    (ProjectivePhaseDefect.CM.Construction.rationalCechManifoldForm (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2
      (DivisorClass.Chern.LogCech.RationalCech.logDefectCech (TopCat.of M) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
        (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol) (ProjectiveChernCocycle.CM.Construction.projectiveLogCech_cocycle p hp hhol)))

theorem projective_curvature_rational_defect_boundary :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)).d 1 2
      (ConnectionTransgression.CM.Construction.connectionTotalPrimitive (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
        (ProjectiveConnectionCech.CM.Construction.projectiveConnectionCech p hp hhol) (ProjectiveConnectionCech.CM.Construction.projectivePhaseCech p hp hhol)) =
      (projectiveCurvatureTotalCocycle p hp hhol).val - projectiveRationalDefectTotal p hp hhol := by
  refine (ProjectiveConnectionCech.CM.Construction.projective_curvature_logarithmic_boundary p hp hhol).trans ?_
  exact congrArg (fun c : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 0 2 =>
    (projectiveCurvatureTotalCocycle p hp hhol).val -
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2 0 2 rfl c)
      (ProjectivePhaseDefect.CM.Construction.projectivePhaseCech_delta p hp hhol)

def projectiveRationalDefectCocycle :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainCocycles (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2 :=
  ⟨projectiveRationalDefectTotal p hp hhol,
    cochain_closed_of_difference_boundary _ (projectiveCurvatureTotalCocycle p hp hhol)
      (ConnectionTransgression.CM.Construction.connectionTotalPrimitive (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
        (ProjectiveConnectionCech.CM.Construction.projectiveConnectionCech p hp hhol) (ProjectiveConnectionCech.CM.Construction.projectivePhaseCech p hp hhol)) _
      (projective_curvature_rational_defect_boundary p hp hhol)⟩

theorem projective_curvature_total_class :
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2
      (projectiveCurvatureTotalCocycle p hp hhol) =
    AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)) 2
      (projectiveRationalDefectCocycle p hp hhol) := by
  apply (AlgebraicTopology.Cohomology.Singular.Representatives.cochainClass_eq_iff_exists_succ _ 1 _ _).mpr
  exact ⟨ConnectionTransgression.CM.Construction.connectionTotalPrimitive (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
    (ProjectiveConnectionCech.CM.Construction.projectiveConnectionCech p hp hhol) (ProjectiveConnectionCech.CM.Construction.projectivePhaseCech p hp hhol),
      projective_curvature_rational_defect_boundary p hp hhol⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureDefect.CM.Construction
