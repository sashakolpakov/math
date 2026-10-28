import OAI.Analysis.PDE.Weak.Elliptic.RegularityProduct

noncomputable section
open Set _root_.MeasureTheory InnerProductSpace
namespace OAI.Analysis.PDE.Weak

variable {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

omit [SecondCountableTopology X] in
/-- Local weak derivatives become global after multiplication by an operator
field supported within the local domain. -/
theorem HasWeakDirectionalDerivativeOn.operator_apply_global
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    {Ω : Set X} {v : X} (A : X → E →L[ℝ] F) (hA : ContDiff ℝ 1 A)
    (hAs : tsupport A ⊆ Ω)
    (u g : Lp E 2 μ) (hg : HasWeakDirectionalDerivativeOn μ Ω v u g) :
    HasWeakDirectionalDerivative μ v (fun x ↦ A x (u x))
      (fun x ↦ A x (g x) + fderiv ℝ A x v (u x)) := by
  intro φ hφ hs
  let adj : (E →L[ℝ] F) →L[ℝ] F →L[ℝ] E :=
    ContinuousLinearMap.adjoint.toContinuousLinearEquiv.toContinuousLinearMap
  let B : X → E := fun x ↦ adj (A x) (φ x)
  let C : X → E := fun x ↦ adj (fderiv ℝ A x v) (φ x)
  let D : X → E := fun x ↦ adj (A x) (fderiv ℝ φ x v)
  have hB : ContDiff ℝ 1 B := (adj.contDiff.comp hA).clm_apply hφ
  have hBs : HasCompactSupport B := hasCompactSupport_operator_apply _ hs
  have hBsub : tsupport B ⊆ Ω := by
    apply Subset.trans ?_ hAs
    apply closure_minimal _ (isClosed_tsupport A)
    intro x hx
    by_contra hn
    apply hx
    change adj (A x) (φ x) = 0
    rw [image_eq_zero_of_notMem_tsupport hn, map_zero, zero_apply]
  have hC : Continuous C := by
    have hDA := hA.continuous_fderiv one_ne_zero
    dsimp [C]
    fun_prop
  have hD : Continuous D := by
    have hDφ := hφ.continuous_fderiv one_ne_zero
    dsimp [D]
    fun_prop
  have hCs : HasCompactSupport C := hasCompactSupport_operator_apply _ hs
  have hDs : HasCompactSupport D := hasCompactSupport_operator_apply _ (hs.fderiv_apply ℝ v)
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
      inner ℝ (u x) (D x) := ((A x).adjoint_inner_right (u x) (fderiv ℝ φ x v)).symm
  simp_rw [hleft, hright]
  rw [integral_add hbint hcint]
  linarith

end OAI.Analysis.PDE.Weak
