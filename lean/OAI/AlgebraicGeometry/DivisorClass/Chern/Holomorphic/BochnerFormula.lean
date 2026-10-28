import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultAdjointHessian
import OAI.AlgebraicGeometry.DivisorClass.Chern.DolbeaultTraceHessian

/-! # Bochner Formula -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The original smooth Dolbeault Laplacian is the Hessian trace plus explicit Hessian commutators. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

theorem Holomorphic.BochnerFormula.holomorphicLineSmoothForm_covector_add (n : ℕ) (a b : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (i : V.analyticSpace) (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n ((a + b).val i).extension z =
      Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i).extension z + Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (b.val i).extension z := by
  change Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n (a.val i + b.val i).extension z = _
  unfold Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm
  rw [Analysis.DifferentialForms.Manifold.Open.SmoothOpenManifoldForm.extension_add, Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart_add]
  ext v
  rfl

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_hessian (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let H := Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z (fun _ => w) =
      -(1 / 2 : ℂ) * (∑ j, (H (b j) (S (b.coord j).toContinuousLinearMap) (fun _ => w) +
        Complex.I * H (b j) (Complex.I • S (b.coord j).toContinuousLinearMap) (fun _ => w))) +
      (1 / 2 : ℂ) * ∑ j,
        ((H (b j) w (fun _ => S (b.coord j).toContinuousLinearMap) - H w (b j) (fun _ => S (b.coord j).toContinuousLinearMap)) +
          Complex.I * (H (b j) (Complex.I • w) (fun _ => S (b.coord j).toContinuousLinearMap) -
            H (Complex.I • w) (b j) (fun _ => S (b.coord j).toContinuousLinearMap))) := by
  let first := (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 0 (HolomorphicLine.AntiForms.holomorphicLineAntiZeroEquiv u ⊤ (h.degreeCodifferential V 0 a.val))).val
  let second := Holomorphic.OneFormProjection.holomorphicLineOnePart u ⊤ Complex.I (h.degreeCodifferential V 1 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)
  have hs := congrArg (fun F : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => F (fun _ => w))
    (Holomorphic.BochnerFormula.holomorphicLineSmoothForm_covector_add V e 1 first second i z)
  simp only [ContinuousAlternatingMap.add_apply] at hs
  have hf := h.projectiveDolbeaultAdjoint_hessian V e he i a hz w
  have hd := h.projectedDegreeCodifferentialOne_dolbeault_hessian V e he i a hz w
  apply (hs.trans (congrArg₂ (fun p q : ℂ => p + q) hf hd)).trans
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end

/-! The pointwise Bochner formula for the original smooth Dolbeault Laplacian, with the original line and projective curvatures. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel)
  (he : e ∈ atlas V.analyticModel V.analyticSpace)

include he

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveCovectorHessian_commutator_scalar
    (U : Opens V.analyticSpace) (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u U 1) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (U ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w t : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension z
    let H := Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension) z
    H v w (fun _ => t) - H w v (fun _ => t) =
      -(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z v w) f) (fun _ => t) +
        Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z ![v, w] * f (fun _ => t) := by
  have hd := congrArg (fun F : Analysis.DifferentialForms.Manifold.Basic.FormValue (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) 1 => F (fun _ => t))
    (h.projectiveCovectorHessian_commutator V e he U a i hz v w)
  simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.neg_apply,
    ContinuousAlternatingMap.add_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at hd
  exact hd

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.smoothDolbeaultLaplacianOne_bochner (i : V.analyticSpace)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (w : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    let S := Analysis.HodgeTheory.Decomposition.KoszulConnection.Constructions.bilinearMetricSharp (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z)
    let f := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension z
    let F := Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 2 h.curvature.val z
    let R := Holomorphic.CovectorCommutator.projectiveBaseConnectionCurvature V e z
    let H := Line.CovectorHessian.lineCovectorHessian 1 (Analysis.HodgeTheory.Decomposition.ProjectiveConnection.Constructions.projectiveConnectionCoefficient V e) (h.projectiveConnectionChart V e i)
      (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val.val i).extension) z
    Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 ((h.smoothDolbeaultLaplacianOne V a).val i).extension z (fun _ => w) =
      -(1 / 2 : ℂ) * (∑ j, (H (b j) (S (b.coord j).toContinuousLinearMap) (fun _ => w) +
        Complex.I * H (b j) (Complex.I • S (b.coord j).toContinuousLinearMap) (fun _ => w))) +
      (1 / 2 : ℂ) * ∑ j,
        (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (R (b j) w) f) (fun _ => S (b.coord j).toContinuousLinearMap) +
          F ![b j, w] * f (fun _ => S (b.coord j).toContinuousLinearMap) +
          Complex.I * (-(Analysis.HodgeTheory.Decomposition.CovectorConnection.Constructions.covectorInfinitesimalAction 1 (R (b j) (Complex.I • w)) f)
              (fun _ => S (b.coord j).toContinuousLinearMap) +
            F ![b j, Complex.I • w] * f (fun _ => S (b.coord j).toContinuousLinearMap))) := by
  have hd := h.smoothDolbeaultLaplacianOne_hessian V e he i a hz w
  apply hd.trans
  apply congrArg₂ (fun p q : ℂ => p + q) rfl
  apply congrArg (fun c : ℂ => (1 / 2 : ℂ) * c)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg₂ (fun p q : ℂ => p + Complex.I * q)
    (h.projectiveCovectorHessian_commutator_scalar V e he ⊤ a.val i ⟨hz.1, trivial, hz.2⟩ _ w _)
    (h.projectiveCovectorHessian_commutator_scalar V e he ⊤ a.val i ⟨hz.1, trivial, hz.2⟩ _ (Complex.I • w) _)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
