import OAI.Analysis.DifferentialForms.Manifold.OpenD
import OAI.Analysis.DifferentialForms.Manifold.Derivative

/-! # Open Equivalence -/

namespace OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence

noncomputable section

/-!
# Forms on an open subset and on its induced manifold

The tangent identification is the derivative of the actual inclusion chart.
The coordinate formula identifies the existing open-domain coefficient forms
with smooth covector fields on the induced open submanifold.
-/

open Set Filter _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] {U : Opens E}

theorem open_chartAt_eq_subtypeCoe (x : U) :
    chartAt E x = U.openPartialHomeomorphSubtypeCoe ⟨x⟩ := by
  rw [Opens.chartAt_eq, chartAt_self_eq, OpenPartialHomeomorph.subtypeRestr_def,
    OpenPartialHomeomorph.trans_refl]

theorem open_chartAt_eq_chartAt (x z : U) : chartAt E x = chartAt E z := rfl

@[simp] theorem open_chartAt_apply (x z : U) : (chartAt E x) z = (z : E) := rfl

@[simp] theorem open_chartAt_source (x : U) : (chartAt E x).source = univ := by
  rw [open_chartAt_eq_subtypeCoe, Opens.openPartialHomeomorphSubtypeCoe_source]

@[simp] theorem open_chartAt_target (x : U) : (chartAt E x).target = (U : Set E) := by
  rw [open_chartAt_eq_subtypeCoe, Opens.openPartialHomeomorphSubtypeCoe_target]

theorem openChart_mem_atlas_iff (e : OpenPartialHomeomorph U E) :
    e ∈ atlas E U ↔ ∃ x : U, e = chartAt E x := by
  change e ∈ (⋃ x : U, {chartAt E x}) ↔ _
  simp only [mem_iUnion, mem_singleton_iff]

theorem openChart_eq_chartAt (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U)
    (x : U) : e = chartAt E x := by
  obtain ⟨z, rfl⟩ := (openChart_mem_atlas_iff e).mp he
  exact open_chartAt_eq_chartAt z x

theorem openChart_target (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U) :
    e.target = (U : Set E) := by
  obtain ⟨x, rfl⟩ := (openChart_mem_atlas_iff e).mp he
  exact open_chartAt_target x

theorem openChart_apply (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U)
    (x : U) : e x = (x : E) := by
  rw [openChart_eq_chartAt e he x]
  exact open_chartAt_apply x x

theorem openChart_symm_apply (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U)
    {y : E} (hy : y ∈ U) : e.symm y = ⟨y, hy⟩ := by
  apply Subtype.ext
  rw [← openChart_apply e he (e.symm y)]
  exact e.right_inv (by rwa [openChart_target e he])

variable [NormedSpace ℝ E] {n : ℕ}

/-- The derivative of the inclusion chart identifies the actual tangent space
of the open submanifold with the ambient normed vector space. -/
def openTangentEquiv (x : U) : TangentSpace 𝓘(ℝ, E) x ≃L[ℝ] E :=
  ((mdifferentiable_chart (I := 𝓘(ℝ, E)) x).mfderiv (mem_chart_source E x)).trans
    (NormedSpace.fromTangentSpace ((chartAt E x) x))

@[simp] theorem openTangentEquiv_toContinuousLinearMap (x : U) :
    (openTangentEquiv x).toContinuousLinearMap = Charts.chartTangentMap (chartAt E x) x := rfl

/-- Transport of raw coefficient fields along the actual inclusion tangent map. -/
def openRawManifoldEquiv (U : Opens E) (n : ℕ) :
    (U → Basic.FormValue E n) ≃ₗ[ℂ] Algebra.RawManifoldForm E U n where
  toFun form x := (form x).compContinuousLinearMap (openTangentEquiv x).toContinuousLinearMap
  invFun form x := (form x).compContinuousLinearMap
    (openTangentEquiv x).symm.toContinuousLinearMap
  left_inv form := by
    funext x
    ext v
    change form x (fun i => openTangentEquiv x ((openTangentEquiv x).symm (v i))) = form x v
    congr 1
    funext i
    exact (openTangentEquiv x).apply_symm_apply (v i)
  right_inv form := by
    funext x
    ext v
    change form x (fun i => (openTangentEquiv x).symm (openTangentEquiv x (v i))) = form x v
    congr 1
    funext i
    exact (openTangentEquiv x).symm_apply_apply (v i)
  map_add' form other := by
    funext x
    ext v
    rfl
  map_smul' c form := by
    funext x
    ext v
    rfl

@[simp] theorem openRawManifoldEquiv_apply (form : U → Basic.FormValue E n) (x : U) :
    openRawManifoldEquiv U n form x =
      (form x).compContinuousLinearMap (openTangentEquiv x).toContinuousLinearMap := rfl

@[simp] theorem openRawManifoldEquiv_symm_apply (form : Algebra.RawManifoldForm E U n) (x : U) :
    (openRawManifoldEquiv U n).symm form x =
      (form x).compContinuousLinearMap (openTangentEquiv x).symm.toContinuousLinearMap := rfl

/-- In every induced chart, tangent transport gives exactly the original
open-domain coefficient function. -/
theorem openRawManifoldEquiv_inChart (form : U → Basic.FormValue E n)
    (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U) {y : E} (hy : y ∈ U) :
    (openRawManifoldEquiv U n form).inChart e y = OpenD.openFormExtension U form y := by
  have hyt : y ∈ e.target := by rwa [openChart_target e he]
  have hchart : chartAt E (e.symm y) = e := (openChart_eq_chartAt e he _).symm
  ext v
  change form (e.symm y)
    (fun i => Charts.chartTangentMap (chartAt E (e.symm y)) (e.symm y)
      (Charts.chartInverseTangentMap e y (v i))) = OpenD.openFormExtension U form y v
  rw [hchart]
  have hv : (fun i => Charts.chartTangentMap e (e.symm y) (Charts.chartInverseTangentMap e y (v i))) = v := by
    funext i
    exact congrArg (fun linear => linear (v i)) (Charts.chartTangentMap_comp_inverse e he hyt)
  rw [hv, openChart_symm_apply e he hy]
  exact congrArg (fun value : Basic.FormValue E n => value v)
    (OpenD.openFormExtension_apply U form ⟨y, hy⟩).symm

/-- The chartwise manifold smoothness is exactly the existing open-domain
smoothness under the tangent transport. -/
theorem openRawManifoldEquiv_smooth_iff (form : U → Basic.FormValue E n) :
    Algebra.IsSmoothManifoldFormOn (openRawManifoldEquiv U n form) univ ↔
      ContDiffOn ℝ ∞ (OpenD.openFormExtension U form) (U : Set E) := by
  constructor
  · intro hform y hy
    let x : U := ⟨y, hy⟩
    have hs := hform (chartAt E x) (chart_mem_atlas E x)
    have hs' : ContDiffOn ℝ ∞ ((openRawManifoldEquiv U n form).inChart (chartAt E x))
        (U : Set E) := by
      simpa only [Algebra.manifoldFormChartDomain, preimage_univ, inter_univ,
        open_chartAt_target] using hs
    exact (hs'.congr (fun z hz =>
      (openRawManifoldEquiv_inChart form (chartAt E x) (chart_mem_atlas E x) hz).symm)) y hy
  · intro hform e he
    have hs : ContDiffOn ℝ ∞ ((openRawManifoldEquiv U n form).inChart e) (U : Set E) :=
      hform.congr fun y hy => openRawManifoldEquiv_inChart form e he hy
    simpa only [Algebra.manifoldFormChartDomain, preimage_univ, inter_univ,
      openChart_target e he] using hs

/-- Smooth open-domain forms are precisely smooth forms on the actual induced
open submanifold. The equivalence is complex-linear. -/
def smoothOpenManifoldEquiv (U : Opens E) (n : ℕ) :
    OpenD.SmoothOpenForm U n ≃ₗ[ℂ] Algebra.SmoothManifoldForm E U n where
  toFun form := ⟨openRawManifoldEquiv U n (form : U → Basic.FormValue E n),
    (openRawManifoldEquiv_smooth_iff _).mpr form.smooth⟩
  invFun form := ⟨(openRawManifoldEquiv U n).symm (form : Algebra.RawManifoldForm E U n),
    (openRawManifoldEquiv_smooth_iff _).mp (by
      rw [LinearEquiv.apply_symm_apply]
      exact form.smooth)⟩
  left_inv form := Subtype.ext ((openRawManifoldEquiv U n).left_inv _)
  right_inv form := Subtype.ext ((openRawManifoldEquiv U n).right_inv _)
  map_add' form other := Subtype.ext ((openRawManifoldEquiv U n).map_add _ _)
  map_smul' c form := Subtype.ext ((openRawManifoldEquiv U n).map_smul _ _)

@[simp] theorem smoothOpenManifoldEquiv_apply (form : OpenD.SmoothOpenForm U n) (x : U) :
    smoothOpenManifoldEquiv U n form x =
      (form x).compContinuousLinearMap (openTangentEquiv x).toContinuousLinearMap := rfl

@[simp] theorem smoothOpenManifoldEquiv_symm_apply (form : Algebra.SmoothManifoldForm E U n)
    (x : U) :
    (smoothOpenManifoldEquiv U n).symm form x =
      (form x).compContinuousLinearMap (openTangentEquiv x).symm.toContinuousLinearMap := rfl

/-- The inverse tangent transport reads the coefficients in any induced chart. -/
theorem openRawManifoldEquiv_symm_eq_inChart (form : Algebra.RawManifoldForm E U n)
    (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U) (x : U) :
    (openRawManifoldEquiv U n).symm form x = form.inChart e (x : E) := by
  have h := openRawManifoldEquiv_inChart ((openRawManifoldEquiv U n).symm form)
    e he x.property
  rw [LinearEquiv.apply_symm_apply] at h
  simpa only [OpenD.openFormExtension_apply] using h.symm

/-- The chart expression agrees with the inverse-transported coefficients on a
neighborhood of each domain point, so their actual exterior derivatives agree. -/
theorem openRawManifoldEquiv_inChart_eventuallyEq (form : Algebra.RawManifoldForm E U n)
    (e : OpenPartialHomeomorph U E) (he : e ∈ atlas E U) (x : U) :
    form.inChart e =ᶠ[𝓝 (x : E)]
      OpenD.openFormExtension U ((openRawManifoldEquiv U n).symm form) := by
  filter_upwards [U.isOpen.mem_nhds x.property] with y hy
  have h := openRawManifoldEquiv_inChart ((openRawManifoldEquiv U n).symm form) e he hy
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

/-- Exterior differentiation of manifold forms agrees with differentiation of
their open-domain coefficients. -/
theorem smoothOpenManifoldEquiv_symm_d (form : Algebra.SmoothManifoldForm E U n) :
    (smoothOpenManifoldEquiv U (n + 1)).symm (Algebra.SmoothManifoldForm.d form) =
      OpenD.SmoothOpenForm.d ((smoothOpenManifoldEquiv U n).symm form) := by
  apply OpenD.SmoothOpenForm.ext
  intro x
  let e := chartAt E x
  have he : e ∈ atlas E U := chart_mem_atlas E x
  have hx : (x : E) ∈ e.target := by
    rw [openChart_target e he]
    exact x.property
  change (openRawManifoldEquiv U (n + 1)).symm
    (Algebra.SmoothManifoldForm.d form : Algebra.RawManifoldForm E U (n + 1)) x =
      extDeriv (OpenD.openFormExtension U
        ((openRawManifoldEquiv U n).symm (form : Algebra.RawManifoldForm E U n))) (x : E)
  rw [openRawManifoldEquiv_symm_eq_inChart _ e he x,
    Algebra.SmoothManifoldForm.d_inChart form e he hx]
  exact (openRawManifoldEquiv_inChart_eventuallyEq
    (form : Algebra.RawManifoldForm E U n) e he x).extDeriv_eq

/-- The identification with the induced open manifold intertwines the two
genuine exterior derivatives. -/
theorem smoothOpenManifoldEquiv_d (form : OpenD.SmoothOpenForm U n) :
    Algebra.SmoothManifoldForm.d (smoothOpenManifoldEquiv U n form) =
      smoothOpenManifoldEquiv U (n + 1) (OpenD.SmoothOpenForm.d form) := by
  apply (smoothOpenManifoldEquiv U (n + 1)).symm.injective
  simpa only [LinearEquiv.symm_apply_apply] using
    smoothOpenManifoldEquiv_symm_d (smoothOpenManifoldEquiv U n form)

end

end OAI.Analysis.DifferentialForms.Manifold.OpenEquivalence
