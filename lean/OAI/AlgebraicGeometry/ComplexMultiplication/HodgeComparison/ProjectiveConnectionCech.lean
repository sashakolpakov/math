import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveChernCocycle
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalBerryPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ConnectionTransgression

/-! # Projective Connection Cech -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveConnectionCech.CM.Construction

noncomputable section

section

/-! The actual projective connection and its logarithmic changes,
assembled on the same refined Čech cover as the rational defect class. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [NormalSpace M]
  {ι : Type} [Fintype ι]
  (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

theorem projectiveChernIntersection_subset {n : ℕ} (a : Fin (n + 1) → M × ι) (k : Fin (n + 1)) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a ≤ ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp (a k).2 :=
  (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a k).trans ((ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement p hp hhol).subset (a k))

theorem projectiveLogCech_holomorphic (a : Fin 2 → M × ι) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞ (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol a) :=
  (ProjectiveLogarithmicCover.CM.Construction.projectiveLogRefinement_holomorphic p hp hhol (a 0) (a 1)).comp
    (contMDiff_inclusion (I := 𝓘(ℂ, E)) (n := ∞)
      (le_inf (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 0) (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection_le _ a 1)))

def projectiveChernLift {n : ℕ} (a : Fin (n + 1) → M × ι) (k : Fin (n + 1)) :
    AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a → ι → ℂ :=
  fun x => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a k).2 x.val

theorem projectiveChernLift_holomorphic {n : ℕ} (a : Fin (n + 1) → M × ι) (k : Fin (n + 1)) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞ (projectiveChernLift p hp hhol a k) :=
  (hhol (a k).2).comp_contMDiff (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ∞))
    (fun x => projectiveChernIntersection_subset p hp hhol a k x.property)

theorem projectiveChernLift_nonzero {n : ℕ} (a : Fin (n + 1) → M × ι) (k : Fin (n + 1))
    (x : AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a) :
    projectiveChernLift p hp hhol a k x ≠ 0 :=
  ProjectiveGluing.CM.Construction.projectiveLift_nonzero p hp (a k).2 x.val
    (projectiveChernIntersection_subset p hp hhol a k x.property)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [IsManifold 𝓘(ℂ, E) ∞ M]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def projectiveConnectionCech : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 1 0 :=
  fun a => Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict (projectiveChernIntersection_subset p hp hhol a 0)
    (BerryGauge.CM.Construction.projectiveBerryLocal p hp hhol (a 0).2)

theorem projectiveConnectionCech_d :
    Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 1 0 (projectiveConnectionCech p hp hhol) =
      Analysis.DifferentialForms.Manifold.CechAugmentation.manifoldCechAugmentation (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2 (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol) := by
  funext a
  change Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
    (projectiveChernIntersection_subset p hp hhol a 0) (BerryGauge.CM.Construction.projectiveBerryLocal p hp hhol (a 0).2)) = _
  rw [← Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict_d, BerryGauge.CM.Construction.projectiveBerryLocal_d, Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.restrict_onOpen]
  rfl

theorem projectiveConnectionCech_intrinsic (a : Fin 1 → M × ι) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 1 (projectiveConnectionCech p hp hhol a) =
      BerryLogarithmicDescent.CM.Construction.smoothLiftBerry (projectiveChernLift p hp hhol a 0)
        (projectiveChernLift_holomorphic p hp hhol a 0) (projectiveChernLift_nonzero p hp hhol a 0) := by
  change Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 1 (Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.restrict
    (projectiveChernIntersection_subset p hp hhol a 0)
      (LocalBerryPullback.CM.Construction.localLiftBerry (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp (a 0).2)
        (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a 0).2) (hhol (a 0).2)
        (ProjectiveGluing.CM.Construction.projectiveLift_nonzero p hp (a 0).2))) = _
  rw [LocalBerryPullback.CM.Construction.localLiftBerry_restrict, LocalBerryPullback.CM.Construction.localLiftBerry_intrinsic]
  rfl

def projectivePhaseCech : Analysis.DifferentialForms.Manifold.CechContraction.ManifoldCechCochain (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 0 1 :=
  fun a => (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 0).symm
    (LogarithmicPhase.CM.Construction.logarithmicPhasePrimitive (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol a) (projectiveLogCech_holomorphic p hp hhol a))

theorem projectivePhaseCech_intrinsic (a : Fin 2 → M × ι) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 0 (projectivePhaseCech p hp hhol a) =
      LogarithmicPhase.CM.Construction.logarithmicPhasePrimitive (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol a)
        (projectiveLogCech_holomorphic p hp hhol a) :=
  LinearEquiv.apply_symm_apply _ _

end

/-! The actual Čech coboundary of the local projective connection
is the negative exterior derivative of its logarithmic phase cochain. -/

open _root_.TopologicalSpace Set
open scoped _root_.Manifold ContDiff

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M] [NormalSpace M]
  {ι : Type} [Fintype ι]
  (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)
  (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (ProjectiveGluing.CM.Construction.projectiveLiftDomain p hp i : Set M))

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

def projectiveConnectionOnIntersection {n : ℕ} (a : Fin (n + 1) → M × ι) (k : Fin (n + 1)) :
    Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a) 1 :=
  LocalBerryPullback.CM.Construction.localLiftBerry _ (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a k).2)
    ((hhol (a k).2).mono (projectiveChernIntersection_subset p hp hhol a k))
    (fun x hx => ProjectiveGluing.CM.Construction.projectiveLift_nonzero p hp (a k).2 x
      (projectiveChernIntersection_subset p hp hhol a k hx))

theorem projectiveConnectionOnIntersection_intrinsic {n : ℕ}
    (a : Fin (n + 1) → M × ι) (k : Fin (n + 1)) :
    Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 1 (projectiveConnectionOnIntersection p hp hhol a k) =
      BerryLogarithmicDescent.CM.Construction.smoothLiftBerry (projectiveChernLift p hp hhol a k)
        (projectiveChernLift_holomorphic p hp hhol a k) (projectiveChernLift_nonzero p hp hhol a k) :=
  LocalBerryPullback.CM.Construction.localLiftBerry_intrinsic _ _ _ _

theorem projectiveConnectionCech_delta_apply (a : Fin 2 → M × ι) :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 1 0 (projectiveConnectionCech p hp hhol) a =
      projectiveConnectionOnIntersection p hp hhol a 1 - projectiveConnectionOnIntersection p hp hhol a 0 := by
  have hdelta := AlgebraicTopology.DeRham.Comparison.SmoothCech.cechDelta_apply (Analysis.DifferentialForms.Manifold.ManifoldSheaf.manifoldFormPresheaf E M 1) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
    0 (projectiveConnectionCech p hp hhol) a
  refine hdelta.trans ?_
  rw [Fin.sum_univ_two]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  change (1 : ℤ) • ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a 1).2) x.val v +
    (-1 : ℤ) • ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a 0).2) x.val v =
      ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a 1).2) x.val v -
        ManifoldMetric.CM.Construction.manifoldLiftBerry (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p (a 0).2) x.val v
  simp only [one_smul, neg_one_smul, sub_eq_add_neg]

theorem projectiveConnectionOnIntersection_change (a : Fin 2 → M × ι) :
    projectiveConnectionOnIntersection p hp hhol a 0 - projectiveConnectionOnIntersection p hp hhol a 1 =
      Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (projectivePhaseCech p hp hhol a) := by
  apply (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 1).injective
  have hmap := (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv E _ 1).map_sub
    (projectiveConnectionOnIntersection p hp hhol a 0) (projectiveConnectionOnIntersection p hp hhol a 1)
  refine hmap.trans ?_
  have hpair := congrArg₂ (fun f g : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E
      (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a) 1 => f - g)
    (projectiveConnectionOnIntersection_intrinsic p hp hhol a 0)
    (projectiveConnectionOnIntersection_intrinsic p hp hhol a 1)
  refine hpair.trans ?_
  have hchange := BerryLogarithmicDescent.CM.Construction.smoothLiftBerry_logarithmic_change
    (projectiveChernLift p hp hhol a 0) (projectiveChernLift p hp hhol a 1) (ProjectiveChernCocycle.CM.Construction.projectiveLogCech p hp hhol a)
    (projectiveChernLift_holomorphic p hp hhol a 0) (projectiveChernLift_holomorphic p hp hhol a 1)
    (projectiveLogCech_holomorphic p hp hhol a)
    (projectiveChernLift_nonzero p hp hhol a 0) (projectiveChernLift_nonzero p hp hhol a 1) (by
      intro x
      have hi := projectiveChernIntersection_subset p hp hhol a 0 x.property
      have hj := projectiveChernIntersection_subset p hp hhol a 1 x.property
      rw [ProjectiveChernCocycle.CM.Construction.projectiveLogCech_exp]
      exact Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projective_chart_transition p (a 0).2 (a 1).2 x.val hi hj)
  refine hchange.trans ?_
  have hphase := congrArg Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectivePhaseCech_intrinsic p hp hhol a)
  exact hphase.symm.trans (Analysis.DifferentialForms.Manifold.IntrinsicOpenEquivalence.intrinsicOpenFormEquiv_d (projectivePhaseCech p hp hhol a))

theorem projectiveConnectionCech_delta :
    Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 1 0 (projectiveConnectionCech p hp hhol) =
      -Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechExteriorD (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 0 1 (projectivePhaseCech p hp hhol) := by
  funext a
  rw [projectiveConnectionCech_delta_apply]
  apply Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.ext
  intro x
  ext v
  have h := congrArg (fun f : Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm E
    (AlgebraicTopology.DeRham.Comparison.SmoothCech.cechIntersection (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) a) 1 => f x v)
      (projectiveConnectionOnIntersection_change p hp hhol a)
  change projectiveConnectionOnIntersection p hp hhol a 0 x v -
    projectiveConnectionOnIntersection p hp hhol a 1 x v = _ at h
  change projectiveConnectionOnIntersection p hp hhol a 1 x v -
    projectiveConnectionOnIntersection p hp hhol a 0 x v =
      -((Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.d (projectivePhaseCech p hp hhol a)) x v)
  exact (neg_sub _ _).symm.trans (congrArg Neg.neg h)

theorem projective_curvature_logarithmic_boundary :
    (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)).d 1 2
      (ConnectionTransgression.CM.Construction.connectionTotalPrimitive (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)
        (projectiveConnectionCech p hp hhol) (projectivePhaseCech p hp hhol)) =
      (Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechAugmentationToTotal (E := E) (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol)).f 2
        (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol) -
      Analysis.DifferentialForms.Manifold.CechDeRham.manifoldCechTotalInclusion (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 2 0 2 rfl
        (Analysis.DifferentialForms.Manifold.CechContraction.manifoldCechDelta (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) 0 1 (projectivePhaseCech p hp hhol)) :=
  ConnectionTransgression.CM.Construction.connection_curvature_total_boundary (ProjectiveChernCocycle.CM.Construction.projectiveChernCover p hp hhol) (ProjectiveGluing.CM.Construction.projectiveCurvatureForm p hp hhol)
    (projectiveConnectionCech p hp hhol) (projectivePhaseCech p hp hhol)
    (projectiveConnectionCech_d p hp hhol) (projectiveConnectionCech_delta p hp hhol)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveConnectionCech.CM.Construction
