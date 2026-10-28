import OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricCauchyF
import OAI.AlgebraicGeometry.DivisorClass.Chern.CauchyLocalPrimitive

/-! # Parametric Cauchy Local Primitive -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricCauchyLocalPrimitive

noncomputable section

/-! Local Cauchy primitives with smooth parameters and unchanged holomorphic directions. -/

open _root_.MeasureTheory _root_.Complex Set _root_.Metric
open scoped ContDiff _root_.Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

def localizedParametricCauchyTransform (χ : ℂ → ℝ) (g : P → ℂ → ℂ) : P × ℂ → ℂ :=
  ParametricCauchyF.parametricCauchyTransform (ParametricCauchyF.cutoffCauchyInput χ g)

theorem localizedParametricCauchyTransform_smooth {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → ℂ} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) :
    ContDiffOn ℝ ∞ (localizedParametricCauchyTransform χ g) (S ×ˢ univ) :=
  ParametricCauchyF.parametricCauchyTransform_smooth hS hc.isCompact
    (fun p w _ hw => ParametricCauchyF.cutoffCauchyInput_support χ g p w hw)
    (ParametricCauchyF.cutoffCauchyInput_smooth hχ hS hU hsub hg)

theorem localizedParametricCauchyTransform_primitive {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → ℂ} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    {p : P} (hp : p ∈ S) {w : ℂ} (hw : χ w = 1) :
    CauchyPolarCalculus.complexDbar (fun z => localizedParametricCauchyTransform χ g (p, z)) w = g p w := by
  have h := ParametricCauchyF.parametricCauchyTransform_slice_primitive hc.isCompact
    (fun p z _ hz => ParametricCauchyF.cutoffCauchyInput_support χ g p z hz)
    (ParametricCauchyF.cutoffCauchyInput_smooth hχ hS hU hsub hg) hp w
  change CauchyPolarCalculus.complexDbar (fun z => ParametricCauchyF.parametricCauchyTransform (ParametricCauchyF.cutoffCauchyInput χ g) (p, z)) w = g p w
  simpa only [ParametricCauchyF.cutoffCauchyInput, hw, one_smul] using h

theorem exists_parametric_complexDbar_local_primitive {g : P → ℂ → ℂ}
    {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U)) {x : ℂ} (hx : x ∈ U) :
    ∃ G : P × ℂ → ℂ, ContDiffOn ℝ ∞ G (S ×ˢ univ) ∧
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ U ∧
        ∀ p ∈ S, ∀ w ∈ ball x r, CauchyPolarCalculus.complexDbar (fun z => G (p, z)) w = g p w := by
  obtain ⟨r, hr, hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hx)
  let χ : ContDiffBump x :=
    { rIn := r / 2, rOut := r, rIn_pos := half_pos hr, rIn_lt_rOut := half_lt_self hr }
  have hsupp : tsupport χ ⊆ U := by rwa [χ.tsupport_eq]
  refine ⟨localizedParametricCauchyTransform χ g,
    localizedParametricCauchyTransform_smooth χ.contDiff χ.hasCompactSupport hS hU hsupp hg,
    r / 2, half_pos hr, ?_, ?_⟩
  · exact (ball_subset_closedBall.trans (closedBall_subset_closedBall (half_le_self hr.le))).trans hsub
  · intro p hp w hw
    apply localizedParametricCauchyTransform_primitive χ.contDiff χ.hasCompactSupport hS hU hsupp hg hp
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hw)

variable [NormedSpace ℂ P]

theorem localizedParametricCauchyTransform_preserves_holomorphic_direction {χ : ℂ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {g : P → ℂ → ℂ} {S : Set P} {U : Set ℂ} (hS : IsOpen S) (hU : IsOpen U)
    (hsub : tsupport χ ⊆ U) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (S ×ˢ U))
    (q : P × ℂ) (hq : q.1 ∈ S) (v : P)
    (hv : ∀ w ∈ U, fderiv ℝ (Function.uncurry g) (q.1, w) (I • v, 0) =
      I * fderiv ℝ (Function.uncurry g) (q.1, w) (v, 0)) :
    fderiv ℝ (localizedParametricCauchyTransform χ g) q (I • v, 0) =
      I * fderiv ℝ (localizedParametricCauchyTransform χ g) q (v, 0) := by
  apply ParametricCauchyF.parametricCauchyTransform_preserves_holomorphic_direction hS hc.isCompact
    (fun p w _ hw => ParametricCauchyF.cutoffCauchyInput_support χ g p w hw)
    (ParametricCauchyF.cutoffCauchyInput_smooth hχ hS hU hsub hg) q hq v
  intro w
  by_cases hw : w ∈ U
  · rw [ParametricCauchyF.cutoffCauchyInput_parameterDerivative hχ hS hU hg hq hw,
      ParametricCauchyF.cutoffCauchyInput_parameterDerivative hχ hS hU hg hq hw, hv w hw]
    simp only [real_smul]
    ring
  · rw [ParametricCauchyF.cutoffCauchyInput_fderiv_zero (fun h => hw (hsub h))]
    simp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.ParametricCauchyLocalPrimitive
