import OAI.Analysis.PDE.Weak.Elliptic.LocalDerivative
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
open scoped ContDiff
namespace OAI.Analysis.PDE.Weak

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] [CompleteSpace F] in
theorem tsupport_operator_apply_subset (A : X → E →L[ℝ] F) (φ : X → E) :
    tsupport (fun x ↦ A x (φ x)) ⊆ tsupport φ := by
  apply closure_minimal _ (isClosed_tsupport φ)
  intro x hx
  by_contra hnot
  apply hx
  change A x (φ x) = 0
  rw [image_eq_zero_of_notMem_tsupport hnot, map_zero]

omit [NormedSpace ℝ X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] [CompleteSpace E] [CompleteSpace F] in
theorem hasCompactSupport_operator_apply (A : X → E →L[ℝ] F) {φ : X → E}
    (hs : HasCompactSupport φ) : HasCompactSupport (fun x ↦ A x (φ x)) :=
  hs.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_operator_apply_subset A φ)

omit [NormedSpace ℝ X] [SecondCountableTopology X] [CompleteSpace E] in
theorem integrable_inner_compact_test (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (u : Lp E 2 μ) {φ : X → E} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Integrable (fun x ↦ inner ℝ (u x) (φ x)) μ := by
  have hp : MemLp φ 2 μ := hφ.memLp_of_hasCompactSupport hs
  apply (L2.integrable_inner (𝕜 := ℝ) u (hp.toLp φ)).congr
  filter_upwards [hp.coeFn_toLp] with x hx
  rw [hx]

omit [SecondCountableTopology X] in
/-- The genuine local distributional product rule for a C¹ operator field.
No global bounds on the coefficient or its derivative are required:
all products in the proof are tested on compact support. -/
theorem HasWeakDirectionalDerivativeOn.operator_apply
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    {Ω : Set X} {v : X} (A : X → E →L[ℝ] F) (hA : ContDiff ℝ 1 A)
    (u g : Lp E 2 μ) (hg : HasWeakDirectionalDerivativeOn μ Ω v u g) :
    HasWeakDirectionalDerivativeOn μ Ω v (fun x ↦ A x (u x))
      (fun x ↦ A x (g x) + fderiv ℝ A x v (u x)) := by
  intro φ hφ hs hsub
  let adj : (E →L[ℝ] F) →L[ℝ] F →L[ℝ] E :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  let B : X → E := fun x ↦ adj (A x) (φ x)
  let C : X → E := fun x ↦ adj (fderiv ℝ A x v) (φ x)
  let D : X → E := fun x ↦ adj (A x) (fderiv ℝ φ x v)
  have hB : ContDiff ℝ 1 B := (adj.contDiff.comp hA).clm_apply hφ
  have hBs : HasCompactSupport B := hasCompactSupport_operator_apply _ hs
  have hBsub : tsupport B ⊆ Ω := (tsupport_operator_apply_subset _ φ).trans hsub
  have hC : Continuous C := by
    have hDA := hA.continuous_fderiv one_ne_zero
    dsimp [C]
    fun_prop
  have hD : Continuous D := by
    have hDφ := hφ.continuous_fderiv one_ne_zero
    dsimp [D]
    fun_prop
  have hCs : HasCompactSupport C := hasCompactSupport_operator_apply _ hs
  have hDs : HasCompactSupport D :=
    hasCompactSupport_operator_apply _ (hs.fderiv_apply ℝ v)
  have hder (x : X) : fderiv ℝ B x v = C x + D x := by
    have ha := adj.hasFDerivAt.comp x (hA.differentiable one_ne_zero x).hasFDerivAt
    have hb := (ha.clm_apply (hφ.differentiable one_ne_zero x).hasFDerivAt).fderiv
    simpa [B, C, D, ContinuousLinearMap.comp_apply, add_comm] using congrArg (fun L ↦ L v) hb
  have hbint := integrable_inner_compact_test μ g hB.continuous hBs
  have hcint := integrable_inner_compact_test μ u hC hCs
  have hdint := integrable_inner_compact_test μ u hD hDs
  have he := hg B hB hBs hBsub
  simp_rw [hder, inner_add_right] at he
  rw [integral_add hcint hdint] at he
  have hleft (x : X) :
      inner ℝ (A x (g x) + fderiv ℝ A x v (u x)) (φ x) =
        inner ℝ (g x) (B x) + inner ℝ (u x) (C x) := by
    rw [inner_add_left]
    exact congrArg₂ (· + ·)
      ((A x).adjoint_inner_right (g x) (φ x)).symm
      ((fderiv ℝ A x v).adjoint_inner_right (u x) (φ x)).symm
  have hright (x : X) : inner ℝ (A x (u x)) (fderiv ℝ φ x v) =
      inner ℝ (u x) (D x) := by
    exact ((A x).adjoint_inner_right (u x) (fderiv ℝ φ x v)).symm
  simp_rw [hleft, hright]
  rw [integral_add hbint hcint]
  linarith

omit [SecondCountableTopology X] in
theorem HasWeakDirectionalDerivativeOn.operator_apply_memLp
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    {Ω : Set X} {v : X} (A : X → E →L[ℝ] F) (hA : ContDiff ℝ 1 A)
    {u g : X → E} (hu : MemLp u 2 μ) (hg : MemLp g 2 μ)
    (hd : HasWeakDirectionalDerivativeOn μ Ω v u g) :
    HasWeakDirectionalDerivativeOn μ Ω v (fun x ↦ A x (u x))
      (fun x ↦ A x (g x) + fderiv ℝ A x v (u x)) := by
  have hd' : HasWeakDirectionalDerivativeOn μ Ω v (hu.toLp u) (hg.toLp g) := by
    apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on μ hd
    · filter_upwards [hu.coeFn_toLp] with x hx
      exact fun _ ↦ hx.symm
    · filter_upwards [hg.coeFn_toLp] with x hx
      exact fun _ ↦ hx.symm
  apply OAI.Analysis.PDE.Weak.HasWeakDirectionalDerivativeOn.congr_on μ
    (hd'.operator_apply μ A hA (hu.toLp u) (hg.toLp g))
  · filter_upwards [hu.coeFn_toLp] with x hx
    exact fun _ ↦ congrArg (A x) hx
  · filter_upwards [hu.coeFn_toLp, hg.coeFn_toLp] with x hx hy
    intro _
    rw [hx, hy]

end OAI.Analysis.PDE.Weak
