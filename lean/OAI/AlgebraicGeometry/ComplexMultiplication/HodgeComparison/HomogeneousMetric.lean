import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveMetric
import OAI.Analysis.DifferentialForms.Manifold.OpenPullback
import OAI.AlgebraicTopology.DeRham.Comparison.BidegreeRestriction

/-! # Homogeneous Metric -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HomogeneousMetric.CM.Construction

noncomputable section

/-! The smooth closed Fubini--Study curvature on nonzero homogeneous vectors,
and its pullback along holomorphic maps to that open domain. -/

open scoped ContDiff
open Set _root_.TopologicalSpace

variable {ι : Type*} [Fintype ι]

def nonzeroHomogeneousDomain : Opens (ι → ℂ) :=
  ⟨{w | w ≠ 0}, isOpen_ne_fun continuous_id continuous_const⟩

def homogeneousBerryCovector (w : ι → ℂ) : (ι → ℂ) →L[ℝ] ℂ :=
  (1 / (2 * Real.pi * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq w) : ℝ) •
    ∑ i, ((w i).re • ProjectiveMetric.CM.Construction.imagCoordinateCovector i - (w i).im • ProjectiveMetric.CM.Construction.realCoordinateCovector i)

theorem homogeneousBerryCovector_apply (w u : ι → ℂ) :
    homogeneousBerryCovector w u = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection w (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) u) := by
  rw [homogeneousBerryCovector, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection]
  simp only [smul_apply, sum_apply, sub_apply, ProjectiveMetric.CM.Construction.imagCoordinateCovector, ProjectiveMetric.CM.Construction.realCoordinateCovector,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, Complex.imCLM_apply, Complex.reCLM_apply,
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinatePairing, LinearMap.id_apply, Complex.im_sum, Complex.mul_im,
    Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.real_smul]
  push_cast
  simp only [neg_mul, ← sub_eq_add_neg, Finset.sum_sub_distrib]
  ring

theorem homogeneousBerryCovector_smoothAt {w : ι → ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ homogeneousBerryCovector w := by
  have hre (i : ι) : ContDiff ℝ ∞ (fun z : ι → ℂ => (z i).re) :=
    Complex.reCLM.contDiff.comp (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).contDiff
  have him (i : ι) : ContDiff ℝ ∞ (fun z : ι → ℂ => (z i).im) :=
    Complex.imCLM.contDiff.comp (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℝ] ℂ).contDiff
  have hn : 2 * Real.pi * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq w ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq_pos w hw).ne'
  unfold homogeneousBerryCovector
  refine ContDiffAt.smul
    (f := fun z : ι → ℂ => 1 / (2 * Real.pi * Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq z))
    (g := fun z : ι → ℂ => ∑ i, ((z i).re • ProjectiveMetric.CM.Construction.imagCoordinateCovector i -
      (z i).im • ProjectiveMetric.CM.Construction.realCoordinateCovector i)) ?_ ?_
  · apply contDiffAt_const.div
    · simp only [Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.coordinateNormSq, Complex.normSq_apply]
      fun_prop
    · exact hn
  · fun_prop

def homogeneousBerryRawForm (w : ι → ℂ) : Analysis.DifferentialForms.Manifold.Basic.FormValue (ι → ℂ) 1 :=
  ContinuousAlternatingMap.ofSubsingleton ℝ (ι → ℂ) ℂ (0 : Fin 1)
    (homogeneousBerryCovector w)

theorem homogeneousBerryRawForm_smoothAt {w : ι → ℂ} (hw : w ≠ 0) :
    ContDiffAt ℝ ∞ homogeneousBerryRawForm w :=
  (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := ι → ℂ) (F := ℂ)
    (0 : Fin 1)).toContinuousLinearEquiv.contDiff.contDiffAt.comp w
      (homogeneousBerryCovector_smoothAt hw)

theorem homogeneousBerryRawForm_smoothOn :
    ContDiffOn ℝ ∞ (homogeneousBerryRawForm (ι := ι))
      (nonzeroHomogeneousDomain (ι := ι) : Set (ι → ℂ)) :=
  fun _ hw => (homogeneousBerryRawForm_smoothAt hw).contDiffWithinAt

def homogeneousBerryOneForm : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (nonzeroHomogeneousDomain (ι := ι)) 1 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ofRaw _ homogeneousBerryRawForm homogeneousBerryRawForm_smoothOn

theorem homogeneousBerryCovector_directional {w : ι → ℂ} (hw : w ≠ 0) (u v : ι → ℂ) :
    fderiv ℝ (fun y => homogeneousBerryCovector y v) w u = Complex.ofReal
      (deriv (fun t : ℝ => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection (w + t • u)
        (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) v) 0) := by
  have hb := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection_hasDerivAt_line
    (f := id) (z := w) (contDiffAt_id (n := 2)) hw u v
  simp only [fderiv_id, id_eq] at hb
  change HasDerivAt (fun t : ℝ => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection (w + t • u) LinearMap.id v) _ 0 at hb
  have hr := Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt 0 hb
  have hd : DifferentiableAt ℝ (fun y => homogeneousBerryCovector y v) w :=
    ((ContinuousLinearMap.apply ℝ ℂ v).contDiff.contDiffAt.comp w
      (homogeneousBerryCovector_smoothAt hw)).differentiableAt (by simp)
  rw [hb.deriv]
  apply (hd.hasFDerivAt.hasLineDerivAt u).unique
  simpa only [HasLineDerivAt, Function.comp_def, homogeneousBerryCovector_apply,
    Complex.ofRealCLM_apply] using hr

def homogeneousFubiniStudyTwoForm : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (nonzeroHomogeneousDomain (ι := ι)) 2 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d homogeneousBerryOneForm

theorem homogeneousFubiniStudyTwoForm_closed :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (homogeneousFubiniStudyTwoForm (ι := ι)) = 0 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_squared homogeneousBerryOneForm

theorem homogeneousFubiniStudyTwoForm_apply
    (w : nonzeroHomogeneousDomain (ι := ι)) (v : Fin 2 → (ι → ℂ)) :
    homogeneousFubiniStudyTwoForm w v = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm w (LinearMap.id : (ι → ℂ) →ₗ[ℂ] (ι → ℂ)) (v 0) (v 1)).im := by
  have hc := Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection_curvature
    (f := id) (z := (w : ι → ℂ)) (contDiffAt_id (n := 2)) w.property (v 0) (v 1)
  simp only [fderiv_id, id_eq] at hc
  change deriv (fun t : ℝ => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection ((w : ι → ℂ) + t • v 0) LinearMap.id (v 1)) 0 -
    deriv (fun t : ℝ => Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.berryConnection ((w : ι → ℂ) + t • v 1) LinearMap.id (v 0)) 0 =
    (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm w LinearMap.id (v 0) (v 1)).im at hc
  rw [homogeneousFubiniStudyTwoForm, homogeneousBerryOneForm, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_ofRaw_apply]
  rw [extDeriv_apply ((homogeneousBerryRawForm_smoothAt w.property).differentiableAt (by simp)),
    Fin.sum_univ_two]
  change (1 : ℤ) • fderiv ℝ (fun y => homogeneousBerryCovector y (v 1)) (w : ι → ℂ) (v 0) +
    (-1 : ℤ) • fderiv ℝ (fun y => homogeneousBerryCovector y (v 0)) (w : ι → ℂ) (v 1) = _
  simp only [one_smul, neg_one_smul, ← sub_eq_add_neg,
    homogeneousBerryCovector_directional w.property]
  rw [← Complex.ofReal_sub, hc]

theorem homogeneousFubiniStudyTwoForm_hasBidegree (w : nonzeroHomogeneousDomain (ι := ι)) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree (ι → ℂ) 1 1 (homogeneousFubiniStudyTwoForm w) := by
  intro c v
  change homogeneousFubiniStudyTwoForm w (fun i : Fin 2 => (c : ℂ) • v i) =
    Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter 1 1 c * homogeneousFubiniStudyTwoForm w v
  rw [homogeneousFubiniStudyTwoForm_apply, homogeneousFubiniStudyTwoForm_apply]
  simp only [Analysis.DifferentialForms.Manifold.Bidegree.bidegreeCharacter, pow_one, map_smulₛₗ, starRingEnd_apply,
    LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
  simp only [← mul_assoc, Complex.star_def, Complex.mul_conj,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.ofReal_mul]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
  {U : Opens E} (f : E → ι → ℂ) (hf : ContDiffOn ℂ ∞ f (U : Set E))
  (hn : ∀ x ∈ U, f x ≠ 0)

include hn in
omit [Fintype ι] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] in
theorem nonzero_lift_mapsTo :
    MapsTo f (U : Set E) (nonzeroHomogeneousDomain (ι := ι) : Set (ι → ℂ)) := hn

/-- Pull back the actual homogeneous curvature along a nonvanishing holomorphic lift. -/
def liftedFubiniStudyTwoForm : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U 2 :=
  Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback (V := nonzeroHomogeneousDomain (ι := ι))
    f (hf.restrict_scalars ℝ) (nonzero_lift_mapsTo f hn) homogeneousFubiniStudyTwoForm

theorem liftedFubiniStudyTwoForm_closed :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d (liftedFubiniStudyTwoForm f hf hn) = 0 := by
  rw [liftedFubiniStudyTwoForm, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.d_pullback,
    homogeneousFubiniStudyTwoForm_closed, map_zero]

theorem liftedFubiniStudyTwoForm_apply (x : U) (v : Fin 2 → E) :
    liftedFubiniStudyTwoForm f hf hn x v = Complex.ofReal
      (Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm (f x) (fderiv ℂ f x).toLinearMap (v 0) (v 1)).im := by
  rw [liftedFubiniStudyTwoForm, Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback_apply_vectors,
    homogeneousFubiniStudyTwoForm_apply]
  have hd := (hf.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  rfl

theorem liftedFubiniStudyTwoForm_hasBidegree (x : U) :
    Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (liftedFubiniStudyTwoForm f hf hn x) := by
  change Analysis.DifferentialForms.Manifold.Bidegree.HasBidegree E 1 1 (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback (V := nonzeroHomogeneousDomain (ι := ι))
    f (hf.restrict_scalars ℝ) (nonzero_lift_mapsTo f hn) homogeneousFubiniStudyTwoForm x)
  rw [Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.pullback_apply]
  have hd := (hf.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  rw [hd.fderiv_restrictScalars ℝ]
  exact AlgebraicTopology.DeRham.Comparison.BidegreeRestriction.hasBidegree_pullback (homogeneousFubiniStudyTwoForm_hasBidegree _) (fderiv ℂ f x)

theorem liftedFubiniStudyTwoForm_positive (x : U)
    (hD : Function.Injective (fderiv ℂ f x)) (i : ι)
    (hwi : f x i ≠ 0) (hDi : ∀ u : E, fderiv ℂ f x u i = 0) (u : E) (hu : u ≠ 0) :
    0 < (liftedFubiniStudyTwoForm f hf hn x ![u, Complex.I • u]).re := by
  rw [liftedFubiniStudyTwoForm_apply]
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, map_smul,
    smul_eq_mul, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
    zero_add, Complex.ofReal_re] using
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm_positive (f x) (fderiv ℂ f x).toLinearMap hD i hwi hDi u hu

/-- Multiplying a homogeneous lift by a nonzero holomorphic scalar leaves
the actual pulled-back curvature unchanged. -/
theorem liftedFubiniStudyTwoForm_gauge
    (g : E → ι → ℂ) (hg : ContDiffOn ℂ ∞ g (U : Set E)) (hng : ∀ x ∈ U, g x ≠ 0)
    (a : E → ℂ) (ha : ContDiffOn ℂ ∞ a (U : Set E)) (hna : ∀ x ∈ U, a x ≠ 0)
    (hfg : ∀ x ∈ U, f x = a x • g x) :
    liftedFubiniStudyTwoForm f hf hn = liftedFubiniStudyTwoForm g hg hng := by
  apply Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.ext
  intro x
  ext v
  rw [liftedFubiniStudyTwoForm_apply, liftedFubiniStudyTwoForm_apply]
  have he : f =ᶠ[nhds (x : E)] fun y => a y • g y := by
    filter_upwards [U.isOpen.mem_nhds x.property] with y hy
    exact hfg y hy
  have hda := (ha.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  have hdg := (hg.contDiffAt (U.isOpen.mem_nhds x.property)).differentiableAt (by simp)
  have hD : (fderiv ℂ f x).toLinearMap = a x • (fderiv ℂ g x).toLinearMap +
      (fderiv ℂ a x).toLinearMap.smulRight (g x) := by
    rw [he.fderiv_eq]
    exact congrArg ContinuousLinearMap.toLinearMap (fderiv_smul hda hdg)
  rw [hfg x x.property, hD, Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.Construction.fubiniStudyForm_gauge
    (a x) (hna x x.property) (g x) (hng x x.property)]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HomogeneousMetric.CM.Construction
