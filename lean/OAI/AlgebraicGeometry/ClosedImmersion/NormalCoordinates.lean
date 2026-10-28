/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
This file has been modified.
-/
import OAI.AlgebraicGeometry.ClosedImmersion.AnalyticLeftAt
import OAI.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import OAI.Analysis.Foundations.SplitDerivativeNormalChart

/-! # Normal Coordinates -/

namespace OAI.AlgebraicGeometry.ClosedImmersion.NormalCoordinates.ComplexPoint

noncomputable section

open _root_.AlgebraicGeometry

/-!
# Normal coordinates for smooth closed immersions

The derivative projection here comes from lifted algebraic coordinate sections. The normal
chart is then constructed by the inverse function theorem. Finally the topological
embedding theorem excludes remote branches and identifies the whole local analytic support
with zero normal coordinate.
-/

open _root_.CategoryTheory _root_.Topology Filter

variable (X Y : Over (Spec ↧ℂ))
  (i : Y ⟶ X) (m d : ℕ)
  [SmoothOfRelativeDimension m Y.hom] [SmoothOfRelativeDimension d X.hom]
  [IsClosedImmersion i.left] (z : ComplexPoint.Basic.ComplexSchemePoint Y)

/-- Let `i: Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. In the chosen analytic charts, the derivative of `i` is an
injective complex linear map `ℂ^m → ℂ^d`. This chooses a continuous complex linear left inverse
`P: ℂ^d → ℂ^m`, so `P ∘ D i = id`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection : (Fin d → ℂ) →L[ℂ] (Fin m → ℂ) :=
  (ComplexPoint.Basic.ComplexSchemePoint.exists_leftInverse_fderiv_inclusionInComplexCharts
    X Y i m d z).choose

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).comp
      (fderiv ℂ (ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
        (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)) = ContinuousLinearMap.id ℂ (Fin m → ℂ) :=
  (ComplexPoint.Basic.ComplexSchemePoint.exists_leftInverse_fderiv_inclusionInComplexCharts
    X Y i m d z).choose_spec

/-- Let `i: Y → X` be a closed immersion of smooth complex schemes of dimensions `m,d`, and let `z
∈ Y(ℂ)`. In the chosen charts write `g = e_X ∘ i ∘ e_Y⁻¹` and `a = e_Y(z)`. For the chosen
complex-linear left inverse `P` of `Dg(a)`, this local homeomorphism `ℂ^m × ker P → ℂ^d` is
`(v,w) ↦ g(v)+w` near `(a,0)`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart :
    OpenPartialHomeomorph
      ((Fin m → ℂ) ×
        (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).ker)
      (Fin d → ℂ) :=
  (Analysis.Foundations.SplitDerivativeNormalChart.HasStrictFDerivAt.normalChart (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z).hasStrictFDerivAt)
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z)
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_apply
    (v : (Fin m → ℂ) ×
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).ker) :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z v =
      ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z v.1 + v.2 := rfl

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_source :
    (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).source :=
  (Analysis.Foundations.SplitDerivativeNormalChart.HasStrictFDerivAt.normalChart_mem_source (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z).hasStrictFDerivAt) _ _

theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_target :
    ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z) ∈
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).target := by
  simpa only [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart, ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts_at_center] using
    (Analysis.Foundations.SplitDerivativeNormalChart.HasStrictFDerivAt.normalChart_mem_target (ComplexPoint.Basic.ComplexSchemePoint.analyticAt_inclusionInComplexCharts X Y i m d z).hasStrictFDerivAt)
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_symm_center :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm
      (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) (ComplexPoint.Basic.Point.map i z)) =
        (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by
  simpa using
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).left_inv
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_source X Y i m d z)

/-- The normal space has complex dimension `d - m`. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalKernel_finrank :
    Module.finrank ℂ
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).ker =
        d - m := by
  have hdim :=
    ((Analysis.Foundations.SplitDerivativeNormalChart.ContinuousLinearMap.splitKernelEquiv (fderiv ℂ (ComplexPoint.Basic.ComplexSchemePoint.inclusionInComplexCharts X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z)))
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z)
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection_leftInverse X Y i m d z)).toLinearEquiv.finrank_eq
  simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin] at hdim
  omega

/-- Near the selected ambient point, membership in the entire image is equivalent
to having zero normal coordinate. The forward direction uses the induced topology
to exclude image points whose intrinsic parameters are outside the coordinate neighborhood. -/
private theorem eventually_mem_range_iff_normal_eq_zero :
    ∀ᶠ y in 𝓝 (ComplexPoint.Basic.Point.map i z),
      y ∈ Set.range (ComplexPoint.Basic.Point.map i) ↔
        ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm
          (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) y)).2 = 0 := by
  let eY := ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z
  let eX := ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z)
  let eN := ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z
  let g := ComplexPoint.Basic.Point.map i
  have hzY : z ∈ eY.source := ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source Y m z
  have hzX : g z ∈ eX.source := ComplexPoint.Basic.ComplexSchemePoint.mem_localChart_source X d (g z)
  have hzN : (eY z, 0) ∈ eN.source :=
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_source X Y i m d z
  have hzNt : eX (g z) ∈ eN.target :=
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_mem_target X Y i m d z
  have hcenter : eN.symm (eX (g z)) = (eY z, 0) :=
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_symm_center X Y i m d z
  have hparam : ∀ᶠ w in 𝓝 z, w ∈ eY.source ∧ (eY w, 0) ∈ eN.source := by
    filter_upwards [eY.open_source.mem_nhds hzY,
      ((eY.continuousAt hzY).prodMk continuousAt_const)
        (eN.open_source.mem_nhds hzN)] with w hwY hwN
    exact ⟨hwY, hwN⟩
  rw [(ComplexPoint.Basic.ComplexSchemePoint.isInducing_map_of_closedImmersion i).nhds_eq_comap z, eventually_comap] at hparam
  have hN : ∀ᶠ y in 𝓝 (g z), eX y ∈ eN.target :=
    (eX.continuousAt hzX) (eN.open_target.mem_nhds hzNt)
  have hc : ContinuousAt (fun y => (eN.symm (eX y)).1) (g z) :=
    ((eN.continuousAt_symm hzNt).comp (eX.continuousAt hzX)).fst
  have hback : ∀ᶠ y in 𝓝 (g z),
      g (eY.symm (eN.symm (eX y)).1) ∈ eX.source := by
    have hcont : ContinuousAt (fun y => g (eY.symm (eN.symm (eX y)).1)) (g z) := by
      apply (ComplexPoint.Basic.Point.continuous_map i).continuousAt.comp
      apply ContinuousAt.comp _ hc
      change ContinuousAt eY.symm (eN.symm (eX (g z))).1
      rw [hcenter]
      exact eY.continuousAt_symm (eY.map_source hzY)
    apply hcont (eX.open_source.mem_nhds _)
    change g (eY.symm (eN.symm (eX (g z))).1) ∈ eX.source
    rw [hcenter, eY.left_inv hzY]
    exact hzX
  filter_upwards [hparam, hN, hback, eX.open_source.mem_nhds hzX] with y hpre hyN hyback hyX
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨hwY, hwN⟩ := hpre w rfl
    have hφ : eN (eY w, 0) = eX (g w) := by
      change eX (g (eY.symm (eY w))) + 0 = _
      rw [eY.left_inv hwY, add_zero]
    have heq := eN.left_inv hwN
    rw [hφ] at heq
    exact congrArg Prod.snd heq
  · intro hn
    change (eN.symm (eX y)).2 = 0 at hn
    refine ⟨eY.symm (eN.symm (eX y)).1, ?_⟩
    apply eX.injOn hyback hyX
    have hright := eN.right_inv hyN
    change eX (g (eY.symm (eN.symm (eX y)).1)) + (eN.symm (eX y)).2 = eX y at hright
    rw [hn] at hright
    simpa only [Submodule.coe_zero, add_zero] using hright

/-- An open ambient neighborhood on which normal coordinates detect the full
closed-immersion image, extracted from the neighborhood assertion. -/
theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion :
    ∃ W : Set (ComplexPoint.Basic.ComplexSchemePoint X), IsOpen W ∧ ComplexPoint.Basic.Point.map i z ∈ W ∧
      ∀ y ∈ W, y ∈ Set.range (ComplexPoint.Basic.Point.map i) ↔
        ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm
          (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) y)).2 = 0 := by
  obtain ⟨W, hWsub, hWopen, hzW⟩ := mem_nhds_iff.mp
    (eventually_mem_range_iff_normal_eq_zero X Y i m d z)
  exact ⟨W, hWopen, hzW, hWsub⟩

/-- Let `i: Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. This chart maps a neighborhood of `i(z)` in `X(ℂ)` to `ℂ^m × ker
P`, where `P` is a chosen left inverse of the coordinate derivative of `i`. Throughout its
source, membership in `i(Y(ℂ))` is equivalent to the second coordinate being zero. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint X)
      ((Fin m → ℂ) ×
        (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).ker) :=
  ((ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z)).trans
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm).restrOpen
      (ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion X Y i m d z).choose
      (ComplexPoint.Basic.ComplexSchemePoint.exists_open_normalCriterion X Y i m d z).choose_spec.1

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_apply (y : ComplexPoint.Basic.ComplexSchemePoint X) :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z y =
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart X Y i m d z).symm
        (ComplexPoint.Basic.ComplexSchemePoint.localChart X d (ComplexPoint.Basic.Point.map i z) y) := rfl

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart_center :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z (ComplexPoint.Basic.Point.map i z) =
      (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) :=
  ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalChart_symm_center X Y i m d z

/-- Let `i: Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. Let `P: ℂ^d → ℂ^m` be the chosen left inverse of the derivative of
`i` in analytic coordinates. Since `ker P` has complex dimension `d-m`, this chooses a
continuous complex linear equivalence `ker P ≃ ℂ^{d-m}`. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalKernelEquiv :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionDerivativeProjection X Y i m d z).ker ≃L[ℂ]
      (Fin (d - m) → ℂ) :=
  (LinearEquiv.ofFinrankEq _ _ (by
    simpa only [Module.finrank_pi, Fintype.card_fin] using
      ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalKernel_finrank X Y i m d z)).toContinuousLinearEquiv

/-- Let `i: Y → X` be a closed immersion of smooth schemes over `ℂ`, of respective dimensions `m`
and `d`, and let `z ∈ Y(ℂ)`. This chart maps a neighborhood of `i(z)` in `X(ℂ)` to `ℂ^m ×
ℂ^{d-m}`. Its second coordinate is normal to `Y`, and its zero set throughout the source is
exactly the image of `Y(ℂ)` there. -/
def _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart :
    OpenPartialHomeomorph (ComplexPoint.Basic.ComplexSchemePoint X)
      ((Fin m → ℂ) × (Fin (d - m) → ℂ)) :=
  (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z).trans
    (((ContinuousLinearEquiv.refl ℂ (Fin m → ℂ)).prodCongr
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalKernelEquiv X Y i m d z)).toHomeomorph.toOpenPartialHomeomorph)

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_apply (y : ComplexPoint.Basic.ComplexSchemePoint X) :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z y =
      ((ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z y).1,
        ComplexPoint.Basic.ComplexSchemePoint.closedImmersionNormalKernelEquiv X Y i m d z
          (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z y).2) := rfl

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_source :
    (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z).source =
      (ComplexPoint.Basic.ComplexSchemePoint.closedImmersionFlatteningChart X Y i m d z).source := by
  simp only [ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, Set.preimage_univ, Set.inter_univ]

@[simp] theorem _root_.OAI.AlgebraicGeometry.ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart_center :
    ComplexPoint.Basic.ComplexSchemePoint.closedImmersionStandardFlatteningChart X Y i m d z
      (ComplexPoint.Basic.Point.map i z) = (ComplexPoint.Basic.ComplexSchemePoint.localChart Y m z z, 0) := by simp

end

end OAI.AlgebraicGeometry.ClosedImmersion.NormalCoordinates.ComplexPoint
