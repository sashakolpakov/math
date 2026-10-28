import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerPowersParallel
import OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential

/-! # Kahler Cohomology Functional -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerCohomologyFunctional.CM.Construction

noncomputable section

section

/-! The actual Kähler powers are coclosed. Their metric pairing therefore
annihilates genuine exact forms by the proved global adjoint identity. -/

open OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential.Constructions
open scoped ContDiff _root_.Manifold

theorem smoothForm_zero_of_euclideanCharts (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n)
    (ha : ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel),
      e ∈ atlas V.analyticModel V.analyticSpace →
      ∀ z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e n a.val z = 0) : a = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  let e := chartAt V.analyticModel x
  have he : e ∈ atlas V.analyticModel V.analyticSpace := chart_mem_atlas V.analyticModel x
  have hx : x ∈ e.source := mem_chart_source V.analyticModel x
  let z := (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)
  have hz : z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e := by
    change EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (e x)) ∈ e.target
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact e.map_source hx
  have hchart : a.val.inChart e (e x) = 0 := by
    ext v
    change a.val.inChart e (e x) v = 0
    have h := congrArg (fun c : Analysis.DifferentialForms.Manifold.Basic.FormValue (EuclideanMetric.CM.Construction.varietyEuclideanModel V) n =>
      c (fun i => (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (v i))) (ha e he z hz)
    change a.val.inChart e (EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V z)
      (fun i => EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V ((EuclideanMetric.CM.Construction.varietyEuclideanCoordinates V).symm (v i))) = 0 at h
    simpa only [z, ContinuousLinearEquiv.apply_symm_apply] using h
  rw [← a.val.inChart_comp_chartTangentMap e he hx, hchart]
  ext v
  rfl

theorem projectiveParallel_coclosed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace (n + 1))
    (ha : ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel),
      e ∈ atlas V.analyticModel V.analyticSpace →
      ∀ z ∈ EuclideanMetric.CM.Construction.varietyEuclideanDomain V e, Analysis.HodgeTheory.Decomposition.ProjectiveCovectorConnection.Constructions.projectiveFormCovariantDerivative V e (n + 1) a z = 0) :
    Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V n a = 0 := by
  apply smoothForm_zero_of_euclideanCharts
  intro e he z hz
  have h := Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential.Constructions.projectiveCodifferential_covariant V e he n a hz
  rw [ha e he z hz] at h
  simpa only [zero_apply, map_zero, Finset.sum_const_zero, neg_zero] using h

theorem fubiniStudyPower_coclosed (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k n : ℕ)
    (h : k + k = n + 1) :
    Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential V n (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h (Powers.CM.Construction.fubiniStudyPower V k).val) = 0 := by
  apply projectiveParallel_coclosed
  intro e he z hz
  exact KahlerPowersParallel.CM.Construction.projectiveParallel_degreeCast V e h (Powers.CM.Construction.fubiniStudyPower V k).val z
    (KahlerPowersParallel.CM.Construction.fubiniStudyPower_parallel V e he k hz)

theorem fubiniStudyPower_pair_exact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k n : ℕ)
    (h : k + k = n + 1) (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V (n + 1) (AlgebraicTopology.Kunneth.ManifoldWedge.Constructions.manifoldDegreeCast h (Powers.CM.Construction.fubiniStudyPower V k).val)
      (Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d a) = 0 := by
  rw [Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveCodifferential_pair, fubiniStudyPower_coclosed, Analysis.HodgeTheory.Decomposition.AdjointAlgebra.Constructions.projectiveL2Pair_zero_left]

end

/-! Pairing with an actual positive-degree Kähler power descends to
genuine de Rham cohomology and then to canonical complex Betti cohomology. -/

open OAI.Analysis.HodgeTheory.Decomposition.ProjectiveCovariantCodifferential.Constructions

def projectiveMetricPairLinear (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n) :
    Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm V.analyticModel V.analyticSpace n →ₗ[ℂ] ℂ where
  toFun b := Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V n a b
  map_add' b c := by
    rw [← Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_inner, map_add, inner_add_right]
    rw [Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_inner, Analysis.HodgeTheory.Decomposition.Form.Constructions.smoothToProjectiveL2_inner]
  map_smul' z b := Analysis.HodgeTheory.Decomposition.AdjointManifold.Constructions.projectiveL2Pair_smul_right V n a b z

def fubiniStudyClosedFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (k + k) →ₗ[ℂ] ℂ :=
  (projectiveMetricPairLinear V (k + k) (Powers.CM.Construction.fubiniStudyPower V k).val).comp
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (k + k)).subtype

theorem fubiniStudyClosedFunctional_exact (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace ((k + 1) + (k + 1)) ≤
      LinearMap.ker (fubiniStudyClosedFunctional V (k + 1)) := by
  intro a ha
  obtain ⟨b, hb⟩ := (Analysis.DifferentialForms.Manifold.ManifoldDeRham.mem_manifoldExactClosedForms_iff V.analyticModel V.analyticSpace
    ((k + 1) + (k + 1)) a).mp ha
  change Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V ((k + 1) + (k + 1)) (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val a.val = 0
  rw [← hb]
  exact fubiniStudyPower_pair_exact V (k + 1) ((k + 1) + k) rfl b

def fubiniStudyQuotientFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient V.analyticModel V.analyticSpace ((k + 1) + (k + 1)) →ₗ[ℂ] ℂ :=
  (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace ((k + 1) + (k + 1))).liftQ
    (fubiniStudyClosedFunctional V (k + 1)) (fubiniStudyClosedFunctional_exact V k)

def fubiniStudyCohomologyFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    V.deRhamCohomology ((k + 1) + (k + 1)) →ₗ[ℂ] ℂ :=
  (fubiniStudyQuotientFunctional V k).comp
    (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso V.analyticModel V.analyticSpace ((k + 1) + (k + 1))).toLinearEquiv.toLinearMap

theorem fubiniStudyCohomologyFunctional_formClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace ((k + 1) + (k + 1))) :
    fubiniStudyCohomologyFunctional V k (V.deRhamClass ((k + 1) + (k + 1)) a) =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V ((k + 1) + (k + 1)) (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val a.val := by
  let e := (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso V.analyticModel V.analyticSpace
    ((k + 1) + (k + 1))).toLinearEquiv
  change fubiniStudyQuotientFunctional V k
    (e (e.symm ((Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldExactClosedForms V.analyticModel V.analyticSpace
      ((k + 1) + (k + 1))).mkQ a))) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

def fubiniStudyBettiFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ) :
    V.complexCohomology ((k + 1) + (k + 1)) →ₗ[ℂ] ℂ :=
  (fubiniStudyCohomologyFunctional V k).comp
    (V.deRhamBettiIso ((k + 1) + (k + 1))).inv.hom

theorem fubiniStudyBettiFunctional_formClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (a : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace ((k + 1) + (k + 1))) :
    fubiniStudyBettiFunctional V k
      ((V.deRhamBettiIso ((k + 1) + (k + 1))).hom (V.deRhamClass ((k + 1) + (k + 1)) a)) =
      Analysis.HodgeTheory.Decomposition.Form.Constructions.projectiveL2Pair V ((k + 1) + (k + 1)) (Powers.CM.Construction.fubiniStudyPower V (k + 1)).val a.val := by
  change fubiniStudyCohomologyFunctional V k
    ((V.deRhamBettiIso ((k + 1) + (k + 1))).inv
      ((V.deRhamBettiIso ((k + 1) + (k + 1))).hom (V.deRhamClass ((k + 1) + (k + 1)) a))) = _
  rw [CategoryTheory.Iso.hom_inv_id_apply]
  exact fubiniStudyCohomologyFunctional_formClass V k a

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerCohomologyFunctional.CM.Construction
