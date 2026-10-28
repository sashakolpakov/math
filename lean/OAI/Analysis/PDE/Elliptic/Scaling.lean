import OAI.Analysis.PDE.Elliptic.LinearCalculus

open InnerProductSpace
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def rescalePoint (z : E) (r : ℝ) (x : E) : E := z + r • x

omit [FiniteDimensional ℝ E] in
theorem rescalePoint_contDiff (z : E) (r : ℝ) :
    ContDiff ℝ ⊤ (rescalePoint z r) := contDiff_const.add (contDiff_id.const_smul r)

omit [FiniteDimensional ℝ E] in
theorem hasFDerivAt_rescalePoint (z : E) (r : ℝ) (x : E) :
    HasFDerivAt (rescalePoint z r) (r • ContinuousLinearMap.id ℝ E) x := by
  change HasFDerivAt (fun y : E ↦ z + r • y) _ x
  have h : HasFDerivAt (fun y : E ↦ z + r • y)
      (0 + r • ContinuousLinearMap.id ℝ E) x :=
    (hasFDerivAt_const z x).add ((hasFDerivAt_id x).const_smul r)
  simpa only [zero_add] using h

theorem gradient_rescalePoint {f : E → ℝ} (hf : Differentiable ℝ f)
    (z : E) (r : ℝ) (x : E) :
    gradient (fun y ↦ f (rescalePoint z r y)) x = r • gradient f (rescalePoint z r x) := by
  have hd : fderiv ℝ (fun y ↦ f (rescalePoint z r y)) x =
      (fderiv ℝ f (rescalePoint z r x)).comp (r • ContinuousLinearMap.id ℝ E) :=
    ((hf (rescalePoint z r x)).hasFDerivAt.comp x (hasFDerivAt_rescalePoint z r x)).fderiv
  have heq : (fderiv ℝ f (rescalePoint z r x)).comp (r • ContinuousLinearMap.id ℝ E) =
      r • fderiv ℝ f (rescalePoint z r x) := by
    ext v
    simp
  rw [gradient, hd, heq, map_smul]
  rfl

theorem fderiv_gradient_rescalePoint {f : E → ℝ} (hf : ContDiff ℝ 2 f)
    (z : E) (r : ℝ) (x : E) :
    fderiv ℝ (gradient (fun y ↦ f (rescalePoint z r y))) x =
      r ^ 2 • fderiv ℝ (gradient f) (rescalePoint z r x) := by
  have hg : gradient (fun y ↦ f (rescalePoint z r y)) =
      fun y ↦ r • gradient f (rescalePoint z r y) :=
    funext (gradient_rescalePoint (hf.differentiable (by norm_num)) z r)
  have hd : HasFDerivAt (fun y ↦ r • gradient f (rescalePoint z r y))
      (r • (fderiv ℝ (gradient f) (rescalePoint z r x)).comp
        (r • ContinuousLinearMap.id ℝ E)) x :=
    (((differentiable_gradient hf (rescalePoint z r x)).hasFDerivAt.comp x
      (hasFDerivAt_rescalePoint z r x)).const_smul r)
  rw [hg, hd.fderiv]
  ext v
  simp [smul_smul, pow_two]

/-- Spatial dilation gives the expected square factor in the actual
variable-coefficient elliptic operator. -/
theorem ellipticTrace_rescalePoint (A : E → E →L[ℝ] E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (z : E) (r : ℝ) (x : E) :
    ellipticTrace (fun y ↦ A (rescalePoint z r y)) (fun y ↦ f (rescalePoint z r y)) x =
      r ^ 2 * ellipticTrace A f (rescalePoint z r x) := by
  unfold ellipticTrace
  rw [fderiv_gradient_rescalePoint hf, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.toLinearMap_smul, map_smul]
  rfl

theorem ellipticTrace_zero (A : E → E →L[ℝ] E) (x : E) :
    ellipticTrace A (fun _ ↦ 0) x = 0 := by
  simp [ellipticTrace]

theorem ellipticTrace_smul (A : E → E →L[ℝ] E) {f : E → ℝ}
    (hf : ContDiff ℝ 2 f) (c : ℝ) (x : E) :
    ellipticTrace A (fun y ↦ c • f y) x = c * ellipticTrace A f x := by
  simpa only [zero_add, ellipticTrace_zero] using
    (ellipticTrace_add_smul A (f := fun _ ↦ 0) contDiff_const hf c x)

end OAI.Analysis.PDE.Elliptic
