import OAI.Analysis.Normed.Function.Holder.C2HolderDirichlet
import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Set Filter
open scoped Topology ContDiff BoundedContinuousFunction
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {X Y E F : Type*}
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance parameterJetFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance parameterJetFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance parameterJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance parameterJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

theorem deriv_clm_curve (L : X →L[ℝ] Y) {u : ℝ → X} {t : ℝ}
    (hu : DifferentiableAt ℝ u t) :
    deriv (fun s ↦ L (u s)) t = L (deriv u t) :=
  (L.hasFDerivAt.comp_hasDerivAt t hu.hasDerivAt).deriv

theorem second_deriv_clm_curve (L : X →L[ℝ] Y) {u : ℝ → X} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u t) :
    deriv (deriv (fun s ↦ L (u s))) t = L (deriv (deriv u) t) := by
  have he : deriv (fun s ↦ L (u s)) =ᶠ[𝓝 t] fun s ↦ L (deriv u s) := by
    filter_upwards [hu.eventually (by norm_num)] with s hs
    exact deriv_clm_curve L (hs.differentiableAt (by norm_num))
  rw [he.deriv_eq]
  exact deriv_clm_curve L ((hu.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num))

theorem deriv_affine_line {f : E → F} {x : E} (v : E)
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun t : ℝ ↦ f (x + t • v)) 0 = fderiv ℝ f x v := by
  have hl : HasDerivAt (fun t : ℝ ↦ x + t • v) v 0 := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hp : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • v) := by simpa using hf.hasFDerivAt
  exact (hp.comp_hasDerivAt 0 hl).deriv

theorem second_deriv_affine_line {f : E → F} {x : E} (v : E)
    (hf : ContDiffAt ℝ 2 f x) :
    deriv (deriv (fun t : ℝ ↦ f (x + t • v))) 0 =
      fderiv ℝ (fderiv ℝ f) x v v := by
  have hl (t : ℝ) : HasDerivAt (fun s : ℝ ↦ x + s • v) v t := by
    simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add x
  have hcont : Tendsto (fun t : ℝ ↦ x + t • v) (𝓝 0) (𝓝 x) := by
    simpa using (show Continuous (fun t : ℝ ↦ x + t • v) from by fun_prop).tendsto 0
  have he : deriv (fun t : ℝ ↦ f (x + t • v)) =ᶠ[𝓝 0]
      fun t ↦ fderiv ℝ f (x + t • v) v := by
    filter_upwards [hcont.eventually (hf.eventually (by norm_num))] with t ht
    exact ((ht.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (hl t)).deriv
  rw [he.deriv_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hv : HasFDerivAt (fun y ↦ fderiv ℝ f y v)
      ((ContinuousLinearMap.apply ℝ F v).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
    (ContinuousLinearMap.apply ℝ F v).hasFDerivAt.comp x hd.hasFDerivAt
  rw [deriv_affine_line v hv.differentiableAt, hv.fderiv]
  rfl

variable {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance parameterHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α) := inferInstance
local instance parameterHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α) := inferInstance

def jetValueEvaluation (x : K) : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α →L[ℝ] F :=
  (BoundedContinuousFunction.evalCLM ℝ x : (K →ᵇ F) →L[ℝ] F).comp
    (OAI.Analysis.Normed.Function.Holder.C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))

theorem value_deriv_curve {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α} {t : ℝ}
    (hU : DifferentiableAt ℝ U t) (x : K) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (deriv U t) x = deriv (fun s ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x) t := by
  let L : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α →L[ℝ] F :=
    jetValueEvaluation (F := F) (hΩK := hΩK) (α := α) x
  have hd : HasDerivAt (fun s ↦ L (U s)) (L (deriv U t)) t :=
    L.hasFDerivAt.comp_hasDerivAt t hU.hasDerivAt
  exact hd.deriv.symm

theorem value_second_deriv_curve {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α} {t : ℝ}
    (hU : ContDiffAt ℝ 2 U t) (x : K) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (deriv (deriv U) t) x =
      deriv (deriv (fun s ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x)) t := by
  let L : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α →L[ℝ] F :=
    jetValueEvaluation (F := F) (hΩK := hΩK) (α := α) x
  exact (second_deriv_clm_curve (X := OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α) (Y := F) L hU).symm

/-- A smooth Banach-valued parameter curve yields an actual C²,α jet of the
second tangential derivative. The original scalar function is only C² here. -/
theorem second_parameter_jet_matches_tangent
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α} (hU : ContDiffAt ℝ 2 U 0)
    (x : K) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → F} {z : V} (v : V) (hf : ContDiffAt ℝ 2 f z)
    (he : (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) x) =ᶠ[𝓝 0] fun t ↦ f (z + t • v)) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (deriv (deriv U) 0) x = fderiv ℝ (fderiv ℝ f) z v v := by
  rw [value_second_deriv_curve hU x, he.deriv.deriv_eq]
  exact second_deriv_affine_line v hf

theorem first_parameter_jet_matches_tangent
    {U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α} (hU : DifferentiableAt ℝ U 0)
    (x : K) {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : V → F} {z : V} (v : V) (hf : DifferentiableAt ℝ f z)
    (he : (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) x) =ᶠ[𝓝 0] fun t ↦ f (z + t • v)) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (deriv U 0) x = fderiv ℝ f z v := by
  rw [value_deriv_curve hU x, he.deriv_eq]
  exact deriv_affine_line v hf

end OAI.Analysis.PDE.Dirichlet
