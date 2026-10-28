import OAI.Analysis.DifferentialForms.Manifold.OpenDerivative
import OAI.Analysis.DifferentialForms.Manifold.OpenPullback

/-! # Chart Equiv -/

namespace OAI.Analysis.DifferentialForms.Manifold

noncomputable section

section

/-!
# Actual forms on a chart source and its coordinate target

The two maps use the genuine tangent derivatives of the chart and its inverse.
Their inverse laws are consequences of the tangent chain rule. Smoothness of
the return map is checked in every manifold chart using the transition map,
and the resulting equivalence commutes with exterior differentiation.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

/-- The source of a chart as an open subset of the manifold. -/
def ChartEquiv.chartSourceOpen (e : OpenPartialHomeomorph M E) : Opens M := ⟨e.source, e.open_source⟩

/-- The target of a chart as an open subset of its model vector space. -/
def ChartEquiv.chartTargetOpen (e : OpenPartialHomeomorph M E) : Opens E := ⟨e.target, e.open_target⟩

section

/-- Transfer coordinate coefficients to actual tangent covectors using a chart. -/
def Algebra.RawManifoldForm.fromChart (e : OpenPartialHomeomorph M E) (form : Basic.RawForm E n) :
    Algebra.RawManifoldForm E M n :=
  fun x => (form (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)

/-- In another chart, this transfer is the ordinary transition-map pullback. -/
theorem Algebra.RawManifoldForm.fromChart_inChart (e f : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (hf : f ∈ atlas E M) (form : Basic.RawForm E n)
    {y : E} (hy : y ∈ f.target) (hey : f.symm y ∈ e.source) :
    (Algebra.RawManifoldForm.fromChart e form).inChart f y =
      (form (e (f.symm y))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) y) := by
  rw [Charts.fderiv_chart_transition f e hf he hy hey]
  ext v
  rfl

/-- Transferring coordinate coefficients back and then using that same chart recovers them. -/
theorem Algebra.RawManifoldForm.inChart_fromChart_apply (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (form : Basic.RawForm E n) {y : E} (hy : y ∈ e.target) :
    (Algebra.RawManifoldForm.fromChart e form).inChart e y = form y := by
  ext v
  change form (e (e.symm y))
      (fun i => Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y (v i))) = form y v
  rw [e.right_inv hy]
  have hv : (fun i => Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y (v i))) = v := by
    funext i
    exact congrArg (fun linear => linear (v i)) (Charts.chartTangentMap_comp_inverse e he hy)
  rw [hv]

/-- Expressing an actual field in a chart and transferring back recovers it on the source. -/
theorem Algebra.RawManifoldForm.fromChart_inChart_apply (e : OpenPartialHomeomorph M E)
    (he : e ∈ atlas E M) (form : Algebra.RawManifoldForm E M n) {x : M} (hx : x ∈ e.source) :
    Algebra.RawManifoldForm.fromChart e (form.inChart e) x = form x := by
  ext v
  change form (e.symm (e x))
      (fun i => Charts.chartInverseTangentMap e (e x) (Charts.chartTangentMap e x (v i))) = form x v
  have hv : (fun i => Charts.chartInverseTangentMap e (e x) (Charts.chartTangentMap e x (v i))) = v := by
    funext i
    exact congrArg (fun linear => linear (v i)) (Charts.chartInverseTangentMap_comp e he hx)
  rw [hv, e.left_inv hx]

/-- Smooth coordinate coefficients give a smooth actual field on the chart source. -/
theorem Algebra.RawManifoldForm.fromChart_smooth (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : Basic.RawForm E n) (hform : ContDiffOn ℝ ∞ form e.target) :
    Algebra.IsSmoothManifoldFormOn (Algebra.RawManifoldForm.fromChart e form) e.source := by
  intro f hf y hy
  have hcoord : ContDiffAt ℝ ∞ (e ∘ f.symm) y :=
    Charts.contDiffAt_chart_transition f e hf he hy.1 hy.2
  have hcoeff : ContDiffAt ℝ ∞ form (e (f.symm y)) :=
    hform.contDiffAt (e.open_target.mem_nhds (e.map_source hy.2))
  have hcomp : ContDiffAt ℝ ∞ (fun z => form (e (f.symm z))) y :=
    ContDiffAt.comp y hcoeff hcoord
  have hsmooth : ContDiffAt ℝ ∞ (fun z =>
      (form (e (f.symm z))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) z)) y :=
    Alternatization.contDiffAt_alternating_compContinuousLinearMap hcomp (hcoord.fderiv_right (by simp))
  have heq : (Algebra.RawManifoldForm.fromChart e form).inChart f =ᶠ[𝓝 y] (fun z =>
      (form (e (f.symm z))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) z)) := by
    filter_upwards [(f.isOpen_inter_preimage_symm e.open_source).mem_nhds hy] with z hz
    exact Algebra.RawManifoldForm.fromChart_inChart e f he hf form hz.1 hz.2
  exact (hsmooth.congr_of_eventuallyEq heq).contDiffWithinAt

end

section

/-- Express a smooth actual section on a chart source in coordinate coefficients. -/
def Open.SmoothOpenManifoldForm.toChart (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) :
    Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n →ₗ[ℂ]
      OpenD.SmoothOpenForm (ChartEquiv.chartTargetOpen e) n where
  toFun form := OpenD.SmoothOpenForm.ofRaw (ChartEquiv.chartTargetOpen e) (form.extension.inChart e)
    ((form.smooth e he).mono (fun _ hy => ⟨hy, e.map_target hy⟩))
  map_add' form other := by
    apply OpenD.SmoothOpenForm.ext
    intro y
    change (form + other).extension.inChart e (y : E) =
      form.extension.inChart e (y : E) + other.extension.inChart e (y : E)
    rw [Open.SmoothOpenManifoldForm.extension_add, Algebra.RawManifoldForm.inChart_add]
    rfl
  map_smul' c form := by
    apply OpenD.SmoothOpenForm.ext
    intro y
    change (c • form).extension.inChart e (y : E) = c • form.extension.inChart e (y : E)
    rw [Open.SmoothOpenManifoldForm.extension_smul, Algebra.RawManifoldForm.inChart_smul]
    rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem Open.SmoothOpenManifoldForm.toChart_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n) (y : ChartEquiv.chartTargetOpen e) :
    Open.SmoothOpenManifoldForm.toChart e he form y = form.extension.inChart e (y : E) := rfl

/-- Transfer a smooth coordinate form to a smooth actual section on the chart source. -/
def Open.SmoothOpenManifoldForm.fromChart (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) :
    OpenD.SmoothOpenForm (ChartEquiv.chartTargetOpen e) n →ₗ[ℂ]
      Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n where
  toFun form := Open.SmoothOpenManifoldForm.ofRaw (ChartEquiv.chartSourceOpen e) (Algebra.RawManifoldForm.fromChart e form.extension)
    (Algebra.RawManifoldForm.fromChart_smooth e he form.extension form.smooth)
  map_add' form other := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change ((form + other).extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) =
      (form.extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) +
        (other.extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)
    rw [OpenD.SmoothOpenForm.extension_add]
    ext v
    rfl
  map_smul' c form := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change ((c • form).extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) =
      c • (form.extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)
    rw [OpenD.SmoothOpenForm.extension_smul]
    ext v
    rfl

@[simp] theorem Open.SmoothOpenManifoldForm.fromChart_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : OpenD.SmoothOpenForm (ChartEquiv.chartTargetOpen e) n) (x : ChartEquiv.chartSourceOpen e) :
    Open.SmoothOpenManifoldForm.fromChart e he form x = Algebra.RawManifoldForm.fromChart e form.extension (x : M) := rfl

@[simp] theorem Open.SmoothOpenManifoldForm.fromChart_toChart (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n) :
    Open.SmoothOpenManifoldForm.fromChart e he (Open.SmoothOpenManifoldForm.toChart e he form) = form := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  have hcoeff : (Open.SmoothOpenManifoldForm.toChart e he form).extension (e x) = form.extension.inChart e (e x) :=
    OpenD.SmoothOpenForm.extension_apply (Open.SmoothOpenManifoldForm.toChart e he form) ⟨e x, e.map_source x.property⟩
  calc
    Open.SmoothOpenManifoldForm.fromChart e he (Open.SmoothOpenManifoldForm.toChart e he form) x =
        Algebra.RawManifoldForm.fromChart e (form.extension.inChart e) (x : M) := by
      change ((Open.SmoothOpenManifoldForm.toChart e he form).extension (e x)).compContinuousLinearMap _ = _
      rw [hcoeff]
      rfl
    _ = form.extension (x : M) :=
      Algebra.RawManifoldForm.fromChart_inChart_apply e he form.extension x.property
    _ = form x := Open.SmoothOpenManifoldForm.extension_apply form x

@[simp] theorem Open.SmoothOpenManifoldForm.toChart_fromChart (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : OpenD.SmoothOpenForm (ChartEquiv.chartTargetOpen e) n) :
    Open.SmoothOpenManifoldForm.toChart e he (Open.SmoothOpenManifoldForm.fromChart e he form) = form := by
  apply OpenD.SmoothOpenForm.ext
  intro y
  have hcoeff : (Open.SmoothOpenManifoldForm.fromChart e he form).extension (e.symm y) =
      Algebra.RawManifoldForm.fromChart e form.extension (e.symm y) :=
    Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.fromChart e he form) ⟨e.symm y, e.map_target y.property⟩
  calc
    Open.SmoothOpenManifoldForm.toChart e he (Open.SmoothOpenManifoldForm.fromChart e he form) y =
        (Algebra.RawManifoldForm.fromChart e form.extension).inChart e (y : E) := by
      change (Open.SmoothOpenManifoldForm.fromChart e he form).extension.inChart e (y : E) = _
      unfold Algebra.RawManifoldForm.inChart
      rw [hcoeff]
    _ = form.extension (y : E) :=
      Algebra.RawManifoldForm.inChart_fromChart_apply e he form.extension y.property
    _ = form y := OpenD.SmoothOpenForm.extension_apply form y

/-- Taking coordinate coefficients intertwines both actual exterior derivatives. -/
theorem Open.SmoothOpenManifoldForm.toChart_d (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n) :
    OpenD.SmoothOpenForm.d (Open.SmoothOpenManifoldForm.toChart e he form) = Open.SmoothOpenManifoldForm.toChart e he (Open.SmoothOpenManifoldForm.d form) := by
  apply OpenD.SmoothOpenForm.ext
  intro y
  have hcoeff : ContDiffOn ℝ ∞ (form.extension.inChart e) (ChartEquiv.chartTargetOpen e : Set E) :=
    (form.smooth e he).mono (fun _ hy => ⟨hy, e.map_target hy⟩)
  change OpenD.SmoothOpenForm.d (OpenD.SmoothOpenForm.ofRaw (ChartEquiv.chartTargetOpen e)
    (form.extension.inChart e) hcoeff) y =
    (Open.SmoothOpenManifoldForm.d form).extension.inChart e (y : E)
  rw [OpenD.SmoothOpenForm.d_ofRaw_apply]
  exact (Open.SmoothOpenManifoldForm.d_inChart form e he ⟨y.property, e.map_target y.property⟩).symm

end

/-- The canonical complex-linear identification of actual forms with chart coefficients. -/
def ChartEquiv.manifoldChartFormEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (n : ℕ) :
    Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n ≃ₗ[ℂ]
      OpenD.SmoothOpenForm (ChartEquiv.chartTargetOpen e) n where
  toLinearMap := Open.SmoothOpenManifoldForm.toChart e he
  invFun := Open.SmoothOpenManifoldForm.fromChart e he
  left_inv := Open.SmoothOpenManifoldForm.fromChart_toChart e he
  right_inv := Open.SmoothOpenManifoldForm.toChart_fromChart e he

theorem ChartEquiv.manifoldChartFormEquiv_d (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartSourceOpen e) n) :
    OpenD.SmoothOpenForm.d (ChartEquiv.manifoldChartFormEquiv e he n form) =
      ChartEquiv.manifoldChartFormEquiv e he (n + 1) (Open.SmoothOpenManifoldForm.d form) :=
  Open.SmoothOpenManifoldForm.toChart_d e he form

end

/-!
# Forms on smaller coordinate neighborhoods

An open subset of a chart target corresponds to its preimage in the chart
source. The genuine local tangent-covector sections on that preimage are
complex-linearly equivalent to smooth alternating forms on the coordinate
open, and this equivalence respects exterior differentiation and restriction.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {n : ℕ}

/-- The portion of a chart source mapping into a coordinate open. -/
def ChartEquiv.chartPreimageOpen (e : OpenPartialHomeomorph M E) (V : Opens E) : Opens M :=
  ⟨e.source ∩ e ⁻¹' (V : Set E), e.isOpen_inter_preimage V.isOpen⟩

/- The chart image of an arbitrary manifold open is restricted to the chart target. -/
def ChartEquiv.chartImageOpen (e : OpenPartialHomeomorph M E) (U : Opens M) : Opens E :=
  ⟨e.target ∩ e.symm ⁻¹' (U : Set M), e.isOpen_inter_preimage_symm U.isOpen⟩

omit [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem ChartEquiv.chartImageOpen_le_target (e : OpenPartialHomeomorph M E) (U : Opens M) :
    ChartEquiv.chartImageOpen e U ≤ ChartEquiv.chartTargetOpen e := fun _ hy => hy.1

omit [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem ChartEquiv.chartPreimage_image_le (e : OpenPartialHomeomorph M E) (U : Opens M) :
    ChartEquiv.chartPreimageOpen e (ChartEquiv.chartImageOpen e U) ≤ U := by
  intro x hx
  have h : e.symm (e x) ∈ U := hx.2.2
  simpa only [e.left_inv hx.1] using h

omit [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem ChartEquiv.mem_chartImageOpen (e : OpenPartialHomeomorph M E) (U : Opens M)
    {x : M} (hx : x ∈ e.source) (hxU : x ∈ U) : e x ∈ ChartEquiv.chartImageOpen e U := by
  refine ⟨e.map_source hx, ?_⟩
  change e.symm (e x) ∈ U
  simpa only [e.left_inv hx] using hxU

omit [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem ChartEquiv.chartPreimageOpen_mono (e : OpenPartialHomeomorph M E)
    {V W : Opens E} (h : W ≤ V) : ChartEquiv.chartPreimageOpen e W ≤ ChartEquiv.chartPreimageOpen e V :=
  fun _ hx => ⟨hx.1, h hx.2⟩

omit [NormedSpace ℝ E] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] in
theorem ChartEquiv.mem_chartPreimageOpen_symm (e : OpenPartialHomeomorph M E)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e) {y : E} (hy : y ∈ V) :
    e.symm y ∈ ChartEquiv.chartPreimageOpen e V := by
  refine ⟨e.map_target (hV hy), ?_⟩
  change e (e.symm y) ∈ V
  simpa only [e.right_inv (hV hy)] using hy

section

/-- Coordinate coefficients smooth only on V suffice on its chart preimage. -/
theorem Algebra.RawManifoldForm.fromChart_smooth_on (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (form : Basic.RawForm E n) (hform : ContDiffOn ℝ ∞ form (V : Set E)) :
    Algebra.IsSmoothManifoldFormOn (Algebra.RawManifoldForm.fromChart e form) (ChartEquiv.chartPreimageOpen e V : Set M) := by
  intro f hf y hy
  have hcoord : ContDiffAt ℝ ∞ (e ∘ f.symm) y :=
    Charts.contDiffAt_chart_transition f e hf he hy.1 hy.2.1
  have hcoeff : ContDiffAt ℝ ∞ form (e (f.symm y)) :=
    hform.contDiffAt (V.isOpen.mem_nhds hy.2.2)
  have hcomp : ContDiffAt ℝ ∞ (fun z => form (e (f.symm z))) y :=
    ContDiffAt.comp y hcoeff hcoord
  have hsmooth : ContDiffAt ℝ ∞ (fun z =>
      (form (e (f.symm z))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) z)) y :=
    Alternatization.contDiffAt_alternating_compContinuousLinearMap hcomp (hcoord.fderiv_right (by simp))
  have heq : (Algebra.RawManifoldForm.fromChart e form).inChart f =ᶠ[𝓝 y] (fun z =>
      (form (e (f.symm z))).compContinuousLinearMap (fderiv ℝ (e ∘ f.symm) z)) := by
    filter_upwards [(f.isOpen_inter_preimage_symm e.open_source).mem_nhds
      ⟨hy.1, hy.2.1⟩] with z hz
    exact Algebra.RawManifoldForm.fromChart_inChart e f he hf form hz.1 hz.2
  exact (hsmooth.congr_of_eventuallyEq heq).contDiffWithinAt

end

section

/-- Coordinate coefficients of a section on the preimage of a coordinate open. -/
def Open.SmoothOpenManifoldForm.toChartOn (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e) :
    Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n →ₗ[ℂ] OpenD.SmoothOpenForm V n where
  toFun form := OpenD.SmoothOpenForm.ofRaw V (form.extension.inChart e)
    ((form.smooth e he).mono (fun _ hy =>
      ⟨hV hy, ChartEquiv.mem_chartPreimageOpen_symm e V hV hy⟩))
  map_add' form other := by
    apply OpenD.SmoothOpenForm.ext
    intro y
    change (form + other).extension.inChart e (y : E) =
      form.extension.inChart e (y : E) + other.extension.inChart e (y : E)
    rw [Open.SmoothOpenManifoldForm.extension_add, Algebra.RawManifoldForm.inChart_add]
    rfl
  map_smul' c form := by
    apply OpenD.SmoothOpenForm.ext
    intro y
    change (c • form).extension.inChart e (y : E) = c • form.extension.inChart e (y : E)
    rw [Open.SmoothOpenManifoldForm.extension_smul, Algebra.RawManifoldForm.inChart_smul]
    rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem Open.SmoothOpenManifoldForm.toChartOn_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n) (y : V) :
    Open.SmoothOpenManifoldForm.toChartOn e he V hV form y = form.extension.inChart e (y : E) := rfl

/-- Smooth coordinate forms determine actual forms on the corresponding chart preimage. -/
def Open.SmoothOpenManifoldForm.fromChartOn (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M) (V : Opens E) :
    OpenD.SmoothOpenForm V n →ₗ[ℂ] Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n where
  toFun form := Open.SmoothOpenManifoldForm.ofRaw (ChartEquiv.chartPreimageOpen e V) (Algebra.RawManifoldForm.fromChart e form.extension)
    (Algebra.RawManifoldForm.fromChart_smooth_on e he V form.extension form.smooth)
  map_add' form other := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change ((form + other).extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) =
      (form.extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) +
        (other.extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)
    rw [OpenD.SmoothOpenForm.extension_add]
    ext v
    rfl
  map_smul' c form := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    change ((c • form).extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x) =
      c • (form.extension (e x)).compContinuousLinearMap (Charts.chartTangentMap e x)
    rw [OpenD.SmoothOpenForm.extension_smul]
    ext v
    rfl

@[simp] theorem Open.SmoothOpenManifoldForm.fromChartOn_apply (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (form : OpenD.SmoothOpenForm V n) (x : ChartEquiv.chartPreimageOpen e V) :
    Open.SmoothOpenManifoldForm.fromChartOn e he V form x = Algebra.RawManifoldForm.fromChart e form.extension (x : M) := rfl

@[simp] theorem Open.SmoothOpenManifoldForm.fromChartOn_toChartOn (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n) :
    Open.SmoothOpenManifoldForm.fromChartOn e he V (Open.SmoothOpenManifoldForm.toChartOn e he V hV form) = form := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  have hcoeff : (Open.SmoothOpenManifoldForm.toChartOn e he V hV form).extension (e x) =
      form.extension.inChart e (e x) :=
    OpenD.SmoothOpenForm.extension_apply (Open.SmoothOpenManifoldForm.toChartOn e he V hV form) ⟨e x, x.property.2⟩
  calc
    Open.SmoothOpenManifoldForm.fromChartOn e he V (Open.SmoothOpenManifoldForm.toChartOn e he V hV form) x =
        Algebra.RawManifoldForm.fromChart e (form.extension.inChart e) (x : M) := by
      change ((Open.SmoothOpenManifoldForm.toChartOn e he V hV form).extension (e x)).compContinuousLinearMap _ = _
      rw [hcoeff]
      rfl
    _ = form.extension (x : M) :=
      Algebra.RawManifoldForm.fromChart_inChart_apply e he form.extension x.property.1
    _ = form x := Open.SmoothOpenManifoldForm.extension_apply form x

@[simp] theorem Open.SmoothOpenManifoldForm.toChartOn_fromChartOn (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e) (form : OpenD.SmoothOpenForm V n) :
    Open.SmoothOpenManifoldForm.toChartOn e he V hV (Open.SmoothOpenManifoldForm.fromChartOn e he V form) = form := by
  apply OpenD.SmoothOpenForm.ext
  intro y
  have hcoeff : (Open.SmoothOpenManifoldForm.fromChartOn e he V form).extension (e.symm y) =
      Algebra.RawManifoldForm.fromChart e form.extension (e.symm y) :=
    Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.fromChartOn e he V form)
      ⟨e.symm y, ChartEquiv.mem_chartPreimageOpen_symm e V hV y.property⟩
  calc
    Open.SmoothOpenManifoldForm.toChartOn e he V hV (Open.SmoothOpenManifoldForm.fromChartOn e he V form) y =
        (Algebra.RawManifoldForm.fromChart e form.extension).inChart e (y : E) := by
      change (Open.SmoothOpenManifoldForm.fromChartOn e he V form).extension.inChart e (y : E) = _
      unfold Algebra.RawManifoldForm.inChart
      rw [hcoeff]
    _ = form.extension (y : E) :=
      Algebra.RawManifoldForm.inChart_fromChart_apply e he form.extension (hV y.property)
    _ = form y := OpenD.SmoothOpenForm.extension_apply form y

/-- The coordinate map on a smaller open commutes with exterior differentiation. -/
theorem Open.SmoothOpenManifoldForm.toChartOn_d (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n) :
    OpenD.SmoothOpenForm.d (Open.SmoothOpenManifoldForm.toChartOn e he V hV form) = Open.SmoothOpenManifoldForm.toChartOn e he V hV (Open.SmoothOpenManifoldForm.d form) := by
  apply OpenD.SmoothOpenForm.ext
  intro y
  have hcoeff : ContDiffOn ℝ ∞ (form.extension.inChart e) (V : Set E) :=
    (form.smooth e he).mono (fun _ hy =>
      ⟨hV hy, ChartEquiv.mem_chartPreimageOpen_symm e V hV hy⟩)
  change OpenD.SmoothOpenForm.d (OpenD.SmoothOpenForm.ofRaw V (form.extension.inChart e) hcoeff) y =
    (Open.SmoothOpenManifoldForm.d form).extension.inChart e (y : E)
  rw [OpenD.SmoothOpenForm.d_ofRaw_apply]
  exact (Open.SmoothOpenManifoldForm.d_inChart form e he
    ⟨hV y.property, ChartEquiv.mem_chartPreimageOpen_symm e V hV y.property⟩).symm

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The coordinate map commutes with restriction to any smaller coordinate open. -/
theorem Open.SmoothOpenManifoldForm.toChartOn_restrict (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    {V W : Opens E} (hV : V ≤ ChartEquiv.chartTargetOpen e) (hWV : W ≤ V)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n) :
    Open.SmoothOpenManifoldForm.toChartOn e he W (hWV.trans hV) (Open.SmoothOpenManifoldForm.restrict (ChartEquiv.chartPreimageOpen_mono e hWV) form) =
      OpenD.SmoothOpenForm.restrict hWV (Open.SmoothOpenManifoldForm.toChartOn e he V hV form) := by
  apply OpenD.SmoothOpenForm.ext
  intro y
  change (Open.SmoothOpenManifoldForm.restrict (ChartEquiv.chartPreimageOpen_mono e hWV) form).extension.inChart e (y : E) =
    form.extension.inChart e (y : E)
  unfold Algebra.RawManifoldForm.inChart
  have hyW := ChartEquiv.mem_chartPreimageOpen_symm e W (hWV.trans hV) y.property
  have hyV := ChartEquiv.mem_chartPreimageOpen_symm e V hV (hWV y.property)
  rw [Open.SmoothOpenManifoldForm.extension_apply (Open.SmoothOpenManifoldForm.restrict (ChartEquiv.chartPreimageOpen_mono e hWV) form) ⟨e.symm y, hyW⟩,
    Open.SmoothOpenManifoldForm.extension_apply form ⟨e.symm y, hyV⟩]
  rfl

end

/-- Actual local manifold forms and coordinate forms on any smaller chart open. -/
def ChartEquiv.manifoldChartOpenFormEquiv (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e) (n : ℕ) :
    Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n ≃ₗ[ℂ] OpenD.SmoothOpenForm V n where
  toLinearMap := Open.SmoothOpenManifoldForm.toChartOn e he V hV
  invFun := Open.SmoothOpenManifoldForm.fromChartOn e he V
  left_inv := Open.SmoothOpenManifoldForm.fromChartOn_toChartOn e he V hV
  right_inv := Open.SmoothOpenManifoldForm.toChartOn_fromChartOn e he V hV

theorem ChartEquiv.manifoldChartOpenFormEquiv_d (e : OpenPartialHomeomorph M E) (he : e ∈ atlas E M)
    (V : Opens E) (hV : V ≤ ChartEquiv.chartTargetOpen e)
    (form : Open.SmoothOpenManifoldForm E (ChartEquiv.chartPreimageOpen e V) n) :
    OpenD.SmoothOpenForm.d (ChartEquiv.manifoldChartOpenFormEquiv e he V hV n form) =
      ChartEquiv.manifoldChartOpenFormEquiv e he V hV (n + 1) (Open.SmoothOpenManifoldForm.d form) :=
  Open.SmoothOpenManifoldForm.toChartOn_d e he V hV form

end

end OAI.Analysis.DifferentialForms.Manifold
