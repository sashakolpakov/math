import OAI.Analysis.ODE.SmoothFlow.Superposition
import OAI.Analysis.ODE.SmoothFlow.Integral
import OAI.Analysis.PDE.Schauder.Calculus.ImplicitFamilyOpen

noncomputable section
open Set Filter Metric
open scoped Topology ContDiff

namespace OAI.Analysis.ODE.SmoothFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The genuine integral equation, with the elapsed time as a parameter. -/
def pathResidual (f : E → E) (hf : Continuous f)
    (p : (E × ℝ) × C(TimeInterval,E)) : C(TimeInterval,E) :=
  p.2 - ContinuousMap.const TimeInterval p.1.1 -
    p.1.2 • volterra (superpose f hf p.2)

theorem contDiff_pathResidual (f : E → E) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (pathResidual f hf.continuous) := by
  have hc : ContDiff ℝ ∞ (fun p : (E×ℝ)×C(TimeInterval,E) =>
      ContinuousMap.const TimeInterval p.1.1) :=
    (ContinuousLinearMap.const ℝ (M:=E) TimeInterval).contDiff.comp contDiff_fst.fst
  exact (contDiff_snd.sub hc).sub
    (contDiff_fst.snd.smul (volterra.contDiff.comp
      ((contDiff_superpose f hf).comp contDiff_snd)))

omit [FiniteDimensional ℝ E] in
theorem pathResidual_zero_time (f : E → E) (hf : Continuous f) (x : E)
    (γ : C(TimeInterval,E)) :
    pathResidual f hf ((x,0),γ) = γ - ContinuousMap.const TimeInterval x := by
  simp only [pathResidual, zero_smul, sub_zero]

theorem pathResidual_partial_zero (f : E → E) (hf : ContDiff ℝ ∞ f) (x : E)
    (γ : C(TimeInterval,E)) :
    (fderiv ℝ (pathResidual f hf.continuous) ((x,0),γ)).comp
      (ContinuousLinearMap.inr ℝ (E×ℝ) C(TimeInterval,E)) =
      ContinuousLinearMap.id ℝ C(TimeInterval,E) := by
  have hi : HasFDerivAt (fun η : C(TimeInterval,E) => ((x,0),η))
      (ContinuousLinearMap.inr ℝ (E×ℝ) C(TimeInterval,E)) γ := by
    convert! (hasFDerivAt_const (x,(0:ℝ)) γ).prodMk (hasFDerivAt_id γ) using 1
  have hd := ((contDiff_pathResidual f hf).differentiable (by simp) ((x,0),γ)).hasFDerivAt.comp γ hi
  have he : (fun η : C(TimeInterval,E) => pathResidual f hf.continuous ((x,0),η)) =
      fun η => η - ContinuousMap.const TimeInterval x := by
    funext η; exact pathResidual_zero_time f hf.continuous x η
  change HasFDerivAt (fun η => pathResidual f hf.continuous ((x,0),η)) _ γ at hd
  rw [he] at hd
  exact hd.unique ((hasFDerivAt_id γ).sub_const _)

/-- A single open parameter set supports an infinitely differentiable family of
actual solutions of the integral equation, confined to a prescribed path ball. -/
theorem exists_smooth_path_family (f : E → E) (hf : ContDiff ℝ ∞ f)
    (x₀ : E) {R : ℝ} (hR : 0<R) :
    ∃ (γ : E×ℝ → C(TimeInterval,E)) (W : Set (E×ℝ)),
      IsOpen W ∧ (x₀,0)∈W ∧ ContDiffOn ℝ ∞ γ W ∧
      γ (x₀,0) = ContinuousMap.const TimeInterval x₀ ∧
      ∀ z∈W, dist (γ z) (ContinuousMap.const TimeInterval x₀) < R ∧
        γ z = ContinuousMap.const TimeInterval z.1 +
          z.2 • volterra (superpose f hf.continuous (γ z)) := by
  let c := ContinuousMap.const TimeInterval x₀
  have hi : ((fderiv ℝ (pathResidual f hf.continuous) ((x₀,0),c)).comp
      (ContinuousLinearMap.inr ℝ (E×ℝ) C(TimeInterval,E))).IsInvertible := by
    rw [pathResidual_partial_zero f hf]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hN : {p : (E×ℝ)×C(TimeInterval,E) | dist p.2 c < R} ∈ 𝓝 ((x₀,0),c) := by
    exact (isOpen_lt (continuous_snd.dist continuous_const) continuous_const).mem_nhds
      (by simpa only [Set.mem_ofPred_eq,dist_self] using hR)
  obtain ⟨γ,W,hW,hW₀,hγ,hγ₀,hsol⟩ :=
    OAI.Analysis.PDE.Schauder.exists_smooth_implicit_family_open (pathResidual f hf.continuous)
      (x₀,(0:ℝ)) c isOpen_univ (contDiff_pathResidual f hf).contDiffOn
      (mem_univ _) (by simp [pathResidual,c]) hi hN
  refine ⟨γ,W,hW,hW₀,hγ,hγ₀,?_⟩
  intro z hz
  refine ⟨(hsol z hz).1,?_⟩
  have he := (hsol z hz).2
  change γ z - ContinuousMap.const TimeInterval z.1 -
    z.2 • volterra (superpose f hf.continuous (γ z)) = 0 at he
  exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).trans (add_comm _ _)

end OAI.Analysis.ODE.SmoothFlow
