import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ManifoldMetric

/-! # Projective Gluing -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveGluing.CM.Construction

noncomputable section

/-! Gluing the actual curvature of holomorphic homogeneous lifts over the
standard projective coordinate cover. -/

open scoped _root_.Manifold ContDiff _root_.Topology
open Set _root_.TopologicalSpace
open OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {ι : Type*} [Fintype ι]

attribute [local instance] Analysis.DifferentialForms.Manifold.ComplexCharts.complexManifold_isRealSmooth

variable (p : M → Projectivization ℂ (ι → ℂ)) (hp : Continuous p)

def projectiveLiftDomain (i : ι) : Opens M :=
  ⟨{x | Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.InPatch i (p x)}, (ComplexPoints.Analytic.ProjectiveCharts.isOpen_projectivePatch i).preimage hp⟩

omit [Fintype ι] in
theorem projectiveLift_cover (x : M) : ∃ i, x ∈ projectiveLiftDomain p hp i :=
  Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.exists_inPatch (p x)

omit [Fintype ι] in
theorem projectiveLift_nonzero (i : ι) (x : M) (hx : x ∈ projectiveLiftDomain p hp i) :
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i x ≠ 0 :=
  Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.normalized_ne_zero i _ hx

variable (hhol : ∀ i, ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ι → ℂ) ∞
  (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) (projectiveLiftDomain p hp i : Set M))

include hhol in
theorem projectiveLiftCurvature_compatible (i j : ι) (x : M)
    (hi : x ∈ projectiveLiftDomain p hp i) (hj : x ∈ projectiveLiftDomain p hp j) :
    ManifoldMetric.CM.Construction.manifoldLiftCurvature (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) x =
      ManifoldMetric.CM.Construction.manifoldLiftCurvature (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p j) x := by
  let S := (projectiveLiftDomain p hp i : Set M) ∩ (projectiveLiftDomain p hp j : Set M)
  have hS : IsOpen S := (projectiveLiftDomain p hp i).isOpen.inter (projectiveLiftDomain p hp j).isOpen
  have hfi := (hhol i).mono (inter_subset_left (s := (projectiveLiftDomain p hp i : Set M))
    (t := (projectiveLiftDomain p hp j : Set M)))
  have hfj := (hhol j).mono (inter_subset_right (s := (projectiveLiftDomain p hp i : Set M))
    (t := (projectiveLiftDomain p hp j : Set M)))
  have hni : ∀ y ∈ S, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i y ≠ 0 :=
    fun y hy => projectiveLift_nonzero p hp i y hy.1
  have hnj : ∀ y ∈ S, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p j y ≠ 0 :=
    fun y hy => projectiveLift_nonzero p hp j y hy.2
  have ha : ContMDiffOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ∞
      (fun y => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i y j) S :=
    contMDiffOn_pi_space.mp hfi j
  have hna : ∀ y ∈ S, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i y j ≠ 0 :=
    fun y hy => (Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.inPatch_iff_ratio_ne_zero i j (p y) hy.1).mp hy.2
  exact ManifoldMetric.CM.Construction.manifoldLiftCurvature_gauge hS _ hfi hni _ hfj hnj _ ha hna
    (fun y hy => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projective_chart_transition p i j y hy.1 hy.2) ⟨hi, hj⟩

def projectiveCurvatureRaw : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 2 :=
  Analysis.DifferentialForms.Manifold.Algebra.glueRawManifoldForm (fun i => (projectiveLiftDomain p hp i : Set M))
    (fun i => ManifoldMetric.CM.Construction.manifoldLiftCurvature (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i))
    (projectiveLift_cover p hp)

include hhol in
theorem projectiveCurvatureRaw_eq (i : ι) {x : M} (hx : x ∈ projectiveLiftDomain p hp i) :
    projectiveCurvatureRaw (E := E) p hp x =
      ManifoldMetric.CM.Construction.manifoldLiftCurvature (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i) x :=
  Analysis.DifferentialForms.Manifold.Algebra.glueRawManifoldForm_eq _ _ (projectiveLift_cover p hp)
    (projectiveLiftCurvature_compatible p hp hhol) i hx

include hhol in
theorem projectiveCurvatureRaw_smooth : Analysis.DifferentialForms.Manifold.Algebra.IsSmoothManifoldFormOn (projectiveCurvatureRaw (E := E) p hp) univ := by
  apply Analysis.DifferentialForms.Manifold.Algebra.isSmooth_glueRawManifoldForm _ _ (projectiveLift_cover p hp)
    (fun i => (projectiveLiftDomain p hp i).isOpen)
  · intro i
    exact ManifoldMetric.CM.Construction.manifoldLiftCurvature_smooth (projectiveLiftDomain p hp i).isOpen _ (hhol i)
      (projectiveLift_nonzero p hp i)
  · exact projectiveLiftCurvature_compatible p hp hhol

/-- The globally glued, genuine smooth projective curvature form. -/
def projectiveCurvatureForm : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M 2 :=
  ⟨projectiveCurvatureRaw p hp, projectiveCurvatureRaw_smooth p hp hhol⟩

theorem projectiveCurvatureForm_closed : Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d (projectiveCurvatureForm p hp hhol) = 0 := by
  apply Analysis.DifferentialForms.Manifold.Algebra.SmoothManifoldForm.ext
  intro x
  obtain ⟨i, hi⟩ := projectiveLift_cover p hp x
  change (projectiveCurvatureRaw (E := E) p hp).exteriorDerivative x = 0
  rw [Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.exteriorDerivative_congr_on _ _ (projectiveLiftDomain p hp i).isOpen
    (fun y hy => projectiveCurvatureRaw_eq p hp hhol i hy) hi]
  exact ManifoldMetric.CM.Construction.manifoldLiftCurvature_closed (projectiveLiftDomain p hp i).isOpen _ (hhol i)
    (projectiveLift_nonzero p hp i) hi

theorem projectiveCurvatureForm_hasBidegree :
    Analysis.DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M 1 1 (projectiveCurvatureForm p hp hhol : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 2) := by
  intro e he y hy
  obtain ⟨i, hi⟩ := projectiveLift_cover p hp (e.symm y)
  have hc : (projectiveCurvatureRaw (E := E) p hp).inChart e y =
      (ManifoldMetric.CM.Construction.manifoldLiftCurvature (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i)).inChart e y := by
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    rw [projectiveCurvatureRaw_eq p hp hhol i hi]
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 ((projectiveCurvatureRaw (E := E) p hp).inChart e y)
  rw [hc]
  exact ManifoldMetric.CM.Construction.manifoldLiftCurvature_hasBidegree (projectiveLiftDomain p hp i).isOpen _ (hhol i)
    (projectiveLift_nonzero p hp i) e he ⟨hy, hi⟩

def projectiveCurvaturePureForm : Analysis.DifferentialForms.Manifold.ManifoldBidegree.PureManifoldForm E M 1 1 :=
  ⟨projectiveCurvatureForm p hp hhol, projectiveCurvatureForm_hasBidegree p hp hhol⟩

theorem projectiveCurvatureForm_inChart_apply (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) (i : ι)
    (hi : e.symm y ∈ projectiveLiftDomain p hp i) (v : Fin 2 → E) :
    (projectiveCurvatureForm p hp hhol : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 2).inChart e y v = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i (e.symm y))
        (fderiv ℂ (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i ∘ e.symm) y).toLinearMap (v 0) (v 1)).im := by
  have hc : (projectiveCurvatureRaw (E := E) p hp).inChart e y =
      (ManifoldMetric.CM.Construction.manifoldLiftCurvature (E := E) (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i)).inChart e y := by
    unfold Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm.inChart
    rw [projectiveCurvatureRaw_eq p hp hhol i hi]
  change (projectiveCurvatureRaw (E := E) p hp).inChart e y v = _
  rw [hc]
  exact ManifoldMetric.CM.Construction.manifoldLiftCurvature_inChart_apply (projectiveLiftDomain p hp i).isOpen _ (hhol i)
    (projectiveLift_nonzero p hp i) e he ⟨hy, hi⟩ v

include hhol in
omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem projectiveLift_fderiv_self (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) (i : ι)
    (hi : e.symm y ∈ projectiveLiftDomain p hp i) (u : E) :
    fderiv ℂ (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i ∘ e.symm) y u i = 0 := by
  have hd := (ManifoldMetric.CM.Construction.manifoldLift_inChart_holomorphic (projectiveLiftDomain p hp i).isOpen _ (hhol i)
    e he ⟨hy, hi⟩).differentiableAt (by simp)
  have hlocal : (fun z => (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i ∘ e.symm) z i) =ᶠ[𝓝 y]
      fun _ => (1 : ℂ) := by
    filter_upwards [(Analysis.DifferentialForms.Manifold.Algebra.isOpen_manifoldFormChartDomain e (projectiveLiftDomain p hp i).isOpen).mem_nhds
      (show y ∈ Analysis.DifferentialForms.Manifold.Algebra.manifoldFormChartDomain e (projectiveLiftDomain p hp i : Set M) from ⟨hy, hi⟩)] with z hz
    exact hz.2
  have hder := hlocal.fderiv_eq (𝕜 := ℂ)
  rw [fderiv_apply hd i] at hder
  simpa using congrArg (fun L : E →L[ℂ] ℂ => L u) hder

/-- At an immersion point the glued projective curvature is positive. -/
theorem projectiveCurvatureForm_positive_inChart (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) {y : E} (hy : y ∈ e.target) (i : ι)
    (hi : e.symm y ∈ projectiveLiftDomain p hp i)
    (hD : Function.Injective (fderiv ℂ (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i ∘ e.symm) y))
    (u : E) (hu : u ≠ 0) :
    0 < ((projectiveCurvatureForm p hp hhol : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm E M 2).inChart e y
      ![u, Complex.I • u]).re := by
  rw [projectiveCurvatureForm_inChart_apply p hp hhol e he hy i hi]
  have hwi : Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i (e.symm y) i ≠ 0 := by
    change Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i i (p (e.symm y)) ≠ 0
    rw [show Foundations.Scheme.ProjectiveCoordinatesIn.Algebraic.ProjectiveCoordinates.ratio i i (p (e.symm y)) = 1 from hi]
    exact one_ne_zero
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_smul,
    smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.ofReal_re] using Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm_positive
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i (e.symm y))
      (fderiv ℂ (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.projectivePullbackChart p i ∘ e.symm) y).toLinearMap hD i hwi
      (projectiveLift_fderiv_self p hp hhol e he hy i hi) u hu

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveGluing.CM.Construction
