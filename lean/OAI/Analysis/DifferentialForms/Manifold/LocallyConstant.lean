import OAI.Analysis.DifferentialForms.Manifold.SectionCoordinates
import OAI.AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms

/-! # Locally Constant -/

namespace OAI

noncomputable section

namespace Analysis.DifferentialForms.Manifold.LocallyConstant

/-!
# The degree-zero exterior kernel on an actual smooth manifold

Local constancy is checked on genuine chart domains. Nullary tangent covectors
have ordinary scalar values, and the existing coordinate derivative and the
proved normed-space kernel theorem identify the manifold exterior kernel.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

/-- Local constancy can be verified on an open neighborhood of every point. -/
theorem isLocallyConstant_of_openNeighborhoods {X Y : Type*} [TopologicalSpace X]
    (f : X → Y)
    (h : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      IsLocallyConstant (fun y : U => f y)) : IsLocallyConstant f := by
  intro s
  apply isOpen_iff_forall_mem_open.2
  intro x hx
  obtain ⟨U, hxU, hU⟩ := h x
  refine ⟨(Subtype.val : U → X) '' ((fun y : U => f y) ⁻¹' s), ?_,
    U.isOpen.isOpenMap_subtype_val _ (hU s), ?_⟩
  · rintro y ⟨z, hz, rfl⟩
    exact hz
  · exact ⟨⟨x, hxU⟩, hx, rfl⟩

section Topology

variable {E : Type*} [NormedAddCommGroup E]
  {M : Type*} [TopologicalSpace M]

/-- The inverse chart, restricted to the chart image of an actual open domain. -/
def chartInverseToOpen (e : OpenPartialHomeomorph M E) (U : Opens M) :
    ChartEquiv.chartImageOpen e U → U := fun y => ⟨e.symm y, y.property.2⟩

theorem chartInverseToOpen_continuous (e : OpenPartialHomeomorph M E) (U : Opens M) :
    Continuous (chartInverseToOpen e U) := by
  apply Continuous.subtype_mk
  exact e.continuousOn_symm.comp_continuous continuous_subtype_val
    (fun y => y.property.1)

variable [ChartedSpace E M]

/-- A scalar section is locally constant exactly when all of its chart expressions are. -/
theorem isLocallyConstant_iff_manifoldCoordinates (U : Opens M) (f : U → ℂ) :
    IsLocallyConstant f ↔
      ∀ (e : OpenPartialHomeomorph M E) (_he : e ∈ atlas E M),
        IsLocallyConstant (fun y : ChartEquiv.chartImageOpen e U => f (chartInverseToOpen e U y)) := by
  constructor
  · intro h e _he
    exact h.comp_continuous (chartInverseToOpen_continuous e U)
  · intro h
    apply isLocallyConstant_of_openNeighborhoods f
    intro x
    let e := chartAt E (x : M)
    have he : e ∈ atlas E M := chart_mem_atlas E (x : M)
    let W : Opens U := ⟨{z : U | (z : M) ∈ e.source},
      e.open_source.preimage continuous_subtype_val⟩
    let q : W → ChartEquiv.chartImageOpen e U := fun z =>
      ⟨e (z.val : M), ChartEquiv.mem_chartImageOpen e U z.property z.val.property⟩
    have hq : Continuous q := by
      apply Continuous.subtype_mk
      exact e.continuousOn.comp_continuous
        (continuous_subtype_val.comp continuous_subtype_val) (fun z => z.property)
    refine ⟨W, mem_chart_source E (x : M), ?_⟩
    have hlocal := (h e he).comp_continuous hq
    have hfun : (fun z : W => f (chartInverseToOpen e U (q z))) =
        (fun z : W => f z.val) := by
      funext z
      apply congrArg f
      apply Subtype.ext
      exact e.left_inv z.property
    exact hfun ▸ hlocal

end Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {U : Opens M}

/-- A genuine smooth manifold zero-form is closed exactly when its scalar section
is locally constant. No connectedness or finite-dimensionality assumption is used. -/
theorem d_openManifoldZeroForm_eq_zero_iff (form : Open.SmoothOpenManifoldForm E U 0) :
    Open.SmoothOpenManifoldForm.d form = 0 ↔
      IsLocallyConstant (fun x : U => form x 0) := by
  rw [Open.SmoothOpenManifoldForm.eq_zero_iff_inChartOn,
    isLocallyConstant_iff_manifoldCoordinates (E := E)]
  constructor
  · intro h e he
    have hd : OpenD.SmoothOpenForm.d (Open.SmoothOpenManifoldForm.inChartOn e he U form) = 0 :=
      (Open.SmoothOpenManifoldForm.inChartOn_d e he U form).trans (h e he)
    have hlocal := (AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.d_openZeroForm_eq_zero_iff
      (Open.SmoothOpenManifoldForm.inChartOn e he U form)).1 hd
    have hfun : (fun y : ChartEquiv.chartImageOpen e U =>
        Open.SmoothOpenManifoldForm.inChartOn e he U form y 0) =
        (fun y : ChartEquiv.chartImageOpen e U => form (chartInverseToOpen e U y) 0) := by
      funext y
      exact Open.SmoothOpenManifoldForm.inChartOn_zero_apply e he U form y
    exact hfun ▸ hlocal
  · intro h e he
    have hd : OpenD.SmoothOpenForm.d (Open.SmoothOpenManifoldForm.inChartOn e he U form) = 0 :=
      (AlgebraicTopology.DeRham.Comparison.LocallyConstantZeroForms.d_openZeroForm_eq_zero_iff
        (Open.SmoothOpenManifoldForm.inChartOn e he U form)).2 (by
          have hfun : (fun y : ChartEquiv.chartImageOpen e U =>
              Open.SmoothOpenManifoldForm.inChartOn e he U form y 0) =
              (fun y : ChartEquiv.chartImageOpen e U => form (chartInverseToOpen e U y) 0) := by
            funext y
            exact Open.SmoothOpenManifoldForm.inChartOn_zero_apply e he U form y
          exact hfun.symm ▸ h e he)
    exact (Open.SmoothOpenManifoldForm.inChartOn_d e he U form).symm.trans hd

end Analysis.DifferentialForms.Manifold.LocallyConstant

namespace Analysis.DifferentialForms.Manifold

/-!
# Locally constant sections as actual smooth manifold zero-forms

The map uses the ordinary nullary alternating covector with the specified
scalar value. Its smoothness is proved in actual charts. Its image is the
actual kernel of the exterior derivative, and restriction is respected.
-/

open Set _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff _root_.Topology

section ScalarExtension

variable {M : Type*} [TopologicalSpace M]

/-- Auxiliary scalar extension; no global smoothness outside U is asserted. -/
def LocallyConstant.manifoldOpenScalarExtension (U : Opens M) (f : U → ℂ) : M → ℂ := by
  classical
  exact fun x => if hx : x ∈ U then f ⟨x, hx⟩ else 0

@[simp]
theorem LocallyConstant.manifoldOpenScalarExtension_apply (U : Opens M) (f : U → ℂ) (x : U) :
    Manifold.LocallyConstant.manifoldOpenScalarExtension U f x = f x := by
  simp [Manifold.LocallyConstant.manifoldOpenScalarExtension, x.property]

/-- The ordinary restriction map for locally constant sections on arbitrary spaces. -/
def LocallyConstant.locallyConstantOpenRestrict {U V : Opens M} (h : V ≤ U) :
    LocallyConstant U ℂ →ₗ[ℂ] LocallyConstant V ℂ where
  toFun f := ⟨fun x => f ⟨x, h x.property⟩,
    f.isLocallyConstant.comp_continuous (continuous_subtype_val.subtype_mk _)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ScalarExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A scalar field defines its usual nullary tangent covector field. -/
def Algebra.RawManifoldForm.ofScalar (f : M → ℂ) : Algebra.RawManifoldForm E M 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ
    (TangentSpace 𝓘(ℝ, E) x) (Fin 0) (f x)

@[simp]
theorem Algebra.RawManifoldForm.ofScalar_apply (f : M → ℂ) (x : M)
    (v : Fin 0 → TangentSpace 𝓘(ℝ, E) x) :
    Algebra.RawManifoldForm.ofScalar (E := E) f x v = f x := rfl

/-- In coordinates a scalar covector remains the same scalar. -/
theorem Algebra.RawManifoldForm.ofScalar_inChart (f : M → ℂ) (e : OpenPartialHomeomorph M E) :
    (Algebra.RawManifoldForm.ofScalar (E := E) f).inChart e =
      fun y => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) (f (e.symm y)) := by
  funext y
  apply ContinuousAlternatingMap.ext
  intro v
  rfl

/-- Local constancy proves chartwise smoothness of the actual scalar covector. -/
theorem LocallyConstant.locallyConstantManifoldZeroForm_smooth (U : Opens M) (f : LocallyConstant U ℂ) :
    Algebra.IsSmoothManifoldFormOn
      (Algebra.RawManifoldForm.ofScalar (E := E) (Manifold.LocallyConstant.manifoldOpenScalarExtension U f)) (U : Set M) := by
  intro e _he
  rw [Algebra.RawManifoldForm.ofScalar_inChart]
  have hlocal : IsLocallyConstant (fun y : ChartEquiv.chartImageOpen e U =>
      Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm y)) := by
    have h := f.isLocallyConstant.comp_continuous (Manifold.LocallyConstant.chartInverseToOpen_continuous e U)
    have hfun : (fun y : ChartEquiv.chartImageOpen e U => Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm y)) =
        (fun y : ChartEquiv.chartImageOpen e U => f (Manifold.LocallyConstant.chartInverseToOpen e U y)) := by
      funext y
      exact Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f (Manifold.LocallyConstant.chartInverseToOpen e U y)
    exact hfun.symm ▸ h
  have hsmooth : ContDiffOn ℝ ∞ (fun y : E => Manifold.LocallyConstant.manifoldOpenScalarExtension U f (e.symm y))
      (Algebra.manifoldFormChartDomain e (U : Set M)) :=
    AlgebraicTopology.DeRham.Comparison.DegreeZeroExactness.contDiffOn_of_isLocallyConstant_on_open
      (Algebra.isOpen_manifoldFormChartDomain e U.isOpen) hlocal
  exact (ContinuousAlternatingMap.constOfIsEmptyLIE ℝ E ℂ (Fin 0)).contDiff.comp_contDiffOn
    hsmooth

variable (E) in
/-- A locally constant section defines the smooth zero-form with those actual values. -/
def LocallyConstant.locallyConstantManifoldZeroForm (U : Opens M) (f : LocallyConstant U ℂ) :
    Open.SmoothOpenManifoldForm E U 0 :=
  Open.SmoothOpenManifoldForm.ofRaw U
    (Algebra.RawManifoldForm.ofScalar (Manifold.LocallyConstant.manifoldOpenScalarExtension U f))
    (Manifold.LocallyConstant.locallyConstantManifoldZeroForm_smooth U f)

@[simp]
theorem LocallyConstant.locallyConstantManifoldZeroForm_apply (U : Opens M) (f : LocallyConstant U ℂ)
    (x : U) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) (x : M)) :
    Manifold.LocallyConstant.locallyConstantManifoldZeroForm E U f x v = f x := by
  change Manifold.LocallyConstant.manifoldOpenScalarExtension U f x = f x
  exact Manifold.LocallyConstant.manifoldOpenScalarExtension_apply U f x

variable (E) in
/-- The actual locally constant inclusion is complex-linear. -/
def LocallyConstant.locallyConstantToManifoldZeroForm (U : Opens M) :
    LocallyConstant U ℂ →ₗ[ℂ] Open.SmoothOpenManifoldForm E U 0 where
  toFun := Manifold.LocallyConstant.locallyConstantManifoldZeroForm E U
  map_add' f g := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply, Open.SmoothOpenManifoldForm.add_apply,
      ContinuousAlternatingMap.add_apply]
    rfl
  map_smul' c f := by
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    simp only [Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply, Open.SmoothOpenManifoldForm.smul_apply,
      ContinuousAlternatingMap.smul_apply]
    rfl

@[simp]
theorem LocallyConstant.locallyConstantToManifoldZeroForm_apply (U : Opens M) (f : LocallyConstant U ℂ)
    (x : U) (v : Fin 0 → TangentSpace 𝓘(ℝ, E) (x : M)) :
    Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f x v = f x :=
  Manifold.LocallyConstant.locallyConstantManifoldZeroForm_apply U f x v

theorem LocallyConstant.locallyConstantToManifoldZeroForm_injective (U : Opens M) :
    Function.Injective (Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U) := by
  intro f g h
  apply DFunLike.ext
  intro x
  have heval := congrArg (fun form : Open.SmoothOpenManifoldForm E U 0 => form x 0) h
  simpa only [Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply] using heval

/-- The actual inclusion commutes with restricting the open domain. -/
theorem LocallyConstant.restrict_locallyConstantToManifoldZeroForm {U V : Opens M} (h : V ≤ U)
    (f : LocallyConstant U ℂ) :
    Open.SmoothOpenManifoldForm.restrict h (Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f) =
      Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E V (Manifold.LocallyConstant.locallyConstantOpenRestrict h f) := by
  apply Open.SmoothOpenManifoldForm.ext
  intro x
  apply ContinuousAlternatingMap.ext
  intro v
  simp only [Open.SmoothOpenManifoldForm.restrict_apply, Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]
  rfl

variable [IsManifold 𝓘(ℝ, E) ∞ M]

@[simp]
theorem LocallyConstant.d_locallyConstantToManifoldZeroForm (U : Opens M) (f : LocallyConstant U ℂ) :
    Open.SmoothOpenManifoldForm.d (Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U f) = 0 := by
  rw [Manifold.LocallyConstant.d_openManifoldZeroForm_eq_zero_iff]
  have hf : IsLocallyConstant (fun x : U => f x) := f.isLocallyConstant
  simpa only [Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply] using hf

/-- Exact image-kernel equality for the genuine manifold degree-zero differential. -/
theorem LocallyConstant.range_locallyConstantToManifoldZeroForm (U : Opens M) :
    LinearMap.range (Manifold.LocallyConstant.locallyConstantToManifoldZeroForm E U) =
      LinearMap.ker (Open.SmoothOpenManifoldForm.d :
        Open.SmoothOpenManifoldForm E U 0 →ₗ[ℂ] Open.SmoothOpenManifoldForm E U 1) := by
  ext form
  constructor
  · rintro ⟨f, rfl⟩
    exact Manifold.LocallyConstant.d_locallyConstantToManifoldZeroForm U f
  · intro h
    let f : LocallyConstant U ℂ :=
      ⟨fun x => form x 0, (Manifold.LocallyConstant.d_openManifoldZeroForm_eq_zero_iff form).1 h⟩
    refine ⟨f, ?_⟩
    apply Open.SmoothOpenManifoldForm.ext
    intro x
    apply ContinuousAlternatingMap.ext
    intro v
    rw [Manifold.LocallyConstant.locallyConstantToManifoldZeroForm_apply]
    change form x 0 = form x v
    congr 1
    exact Subsingleton.elim _ _

end Analysis.DifferentialForms.Manifold

end

end OAI
