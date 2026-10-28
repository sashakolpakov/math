import OAI.Analysis.PDE.Dirichlet.Rough.Parameter.JetExtraction
import OAI.Analysis.Normed.Function.Holder.C2HolderJointParameter

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet.ParameterDeformation

open OAI.Analysis.Normed.Function.Holder

variable {Z T H : Type*}
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Evaluation of a multilinear derivative at fixed directions is bounded linear. -/
def tensorEvaluation (N : ℕ) (v : Fin N → Z) :
    ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ Z) H →L[ℝ] H :=
  LinearMap.mkContinuous
    { toFun := fun A ↦ A v
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    (∏ i, ‖v i‖) (fun A ↦ by
      change ‖A v‖ ≤ (∏ i, ‖v i‖) * ‖A‖
      simpa only [mul_comm] using A.le_opNorm v)

theorem contDiffOn_mixed_derivative {W : Set Z} (hW : IsOpen W)
    {U : Z → H} (hU : ContDiffOn ℝ ∞ U W) (N : ℕ) (v : Fin N → Z) :
    ContDiffOn ℝ ∞ (fun z ↦ iteratedFDeriv ℝ N U z v) W := by
  intro z hz
  have hd : ContDiffAt ℝ ∞ (iteratedFDeriv ℝ N U) z :=
    ((hU z hz).contDiffAt (hW.mem_nhds hz)).iteratedFDeriv_right (by simp)
  exact ((ParameterDeformation.tensorEvaluation N v).contDiff.contDiffAt.comp z hd).contDiffWithinAt

variable {E F : Type*} [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Mixed external/flow derivatives of a smooth stored-jet family retain
joint C² regularity in the remaining external parameter and physical point. -/
theorem contDiffOn_joint_mixed_parameter_value
    {S : Set Z} {W : Set (Z × T)} (hS : IsOpen S) (hW : IsOpen W)
    (hSW : ∀ z ∈ S, (z,(0:T)) ∈ W)
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ} (hΩ : IsOpen Ω)
    (U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α) (hU : ContDiffOn ℝ ∞ U W)
    (N : ℕ) (v : Fin N → Z × T) :
    ContDiffOn ℝ 2 (fun p : Z × E ↦ OAI.Analysis.Normed.Function.Holder.boundedZeroExtension
      (OAI.Analysis.Normed.Function.Holder.C2Holder.value (iteratedFDeriv ℝ N U (p.1,0) v)) p.2) (S ×ˢ Ω) := by
  exact OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_joint_value_smooth hS hΩ
    (fun z ↦ iteratedFDeriv ℝ N U (z,0) v)
    ((ParameterDeformation.contDiffOn_mixed_derivative hW hU N v).comp
      (contDiffOn_id.prodMk contDiffOn_const) hSW)

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] in
/-- The mixed stored derivative is the derivative of the literal
external-parameter/flow translation, using only a germ identity. -/
theorem value_mixed_parameter_eq_of_germ
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    {U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α} {z : Z}
    (hU : ContDiffAt ℝ ∞ U (z,0)) (x : K)
    (f : Z × T → F)
    (he : (fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U ((z,0)+s)) x) =ᶠ[𝓝 0] f)
    (N : ℕ) (v : Fin N → Z × T) :
    OAI.Analysis.Normed.Function.Holder.C2Holder.value (iteratedFDeriv ℝ N U (z,0) v) x =
      iteratedFDeriv ℝ N f 0 v := by
  have hlin := ParameterDeformation.iteratedFDeriv_clm_family
    (jetValueEvaluation (F := F) (hΩK := hΩK) (α := α) x) hU N v
  have hshift : iteratedFDeriv ℝ N
      (fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U ((z,0)+s)) x) 0 v =
      iteratedFDeriv ℝ N (fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x) (z,0) v := by
    have ht := iteratedFDeriv_comp_add_left (𝕜 := ℝ)
      (f := fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U s) x) N (z,0) 0
    exact congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ Z × T) F ↦ A v)
      (by simpa only [add_zero] using ht)
  exact hlin.symm.trans (hshift.symm.trans
    (congrArg (fun A : ContinuousMultilinearMap ℝ (fun _ : Fin N ↦ Z × T) F ↦ A v)
      ((he.iteratedFDeriv ℝ N).eq_of_nhds)))

omit [FiniteDimensional ℝ Z] [FiniteDimensional ℝ E] in
/-- A full spatial translation family gives joint interior smoothness
directly, rather than merely separate parameter and spatial smoothness. -/
theorem contDiffAt_joint_of_translation_family
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    {U : Z × E → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α} {z₀ : Z} {x₀ : E}
    (hx₀ : x₀ ∈ K) (hU : ContDiffAt ℝ ∞ U (z₀,0))
    {f : Z × E → F}
    (he : (fun p : Z × E ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U p) ⟨x₀,hx₀⟩) =ᶠ[𝓝 (z₀,0)]
      fun p ↦ f (p.1,x₀+p.2)) :
    ContDiffAt ℝ ∞ f (z₀,x₀) := by
  have hs : ContDiffAt ℝ ∞ (fun p : Z × E ↦ f (p.1,x₀+p.2)) (z₀,0) :=
    ((jetValueEvaluation (F := F) (hΩK := hΩK) (α := α) ⟨x₀,hx₀⟩).contDiff.contDiffAt.comp
      (z₀,0) hU).congr_of_eventuallyEq he.symm
  have hm : ContDiffAt ℝ ∞ (fun p : Z × E ↦ (p.1,p.2-x₀)) (z₀,x₀) :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sub contDiffAt_const)
  have hs' : ContDiffAt ℝ ∞ (fun p : Z × E ↦ f (p.1,x₀+p.2))
      ((fun p : Z × E ↦ (p.1,p.2-x₀)) (z₀,x₀)) := by
    simpa only [sub_self] using hs
  simpa only [Function.comp_def,← add_sub_assoc,add_sub_cancel_left,Prod.mk.eta]
    using hs'.comp (z₀,x₀) hm

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Mixed external and tangential derivatives on a chart retain joint
C² regularity, before applying the nonlinear normal-derivative bootstrap. -/
theorem contDiffOn_mixed_chart_parameter
    {S : Set Z} {W : Set (Z × T)} (hS : IsOpen S) (hW : IsOpen W)
    (hSW : ∀ z ∈ S, (z,(0:T)) ∈ W)
    {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ} (hΩ : IsOpen Ω)
    (U : Z × T → OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α) (hU : ContDiffOn ℝ ∞ U W)
    {Q : Set X} (G : X → E) (hG : ContDiffOn ℝ 2 G Q) (hGQ : MapsTo G Q Ω)
    (f : Z × X → F) (A : T →L[ℝ] X)
    (he : ∀ z ∈ S, ∀ x (hx : x ∈ Q),
      (fun s : Z × T ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U ((z,0)+s))
        ⟨G x,hΩK (hGQ hx)⟩) =ᶠ[𝓝 0] fun s ↦ f (z+s.1,x+A s.2))
    (N : ℕ) (v : Fin N → Z × T) :
    ContDiffOn ℝ 2 (fun p : Z × X ↦ iteratedFDeriv ℝ N
      (fun s : Z × T ↦ f (p.1+s.1,p.2+A s.2)) 0 v) (S ×ˢ Q) := by
  have hmap : ContDiffOn ℝ 2 (fun p : Z × X ↦ (p.1,G p.2)) (S ×ˢ Q) :=
    contDiffOn_fst.prodMk (hG.comp contDiffOn_snd (fun _ hp ↦ hp.2))
  have hmaps : MapsTo (fun p : Z × X ↦ (p.1,G p.2)) (S ×ˢ Q) (S ×ˢ Ω) :=
    fun _ hp ↦ ⟨hp.1,hGQ hp.2⟩
  apply ((ParameterDeformation.contDiffOn_joint_mixed_parameter_value hS hW hSW hΩ U hU N v).comp hmap hmaps).congr
  intro p hp
  dsimp only [Function.comp_def]
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply _ (hΩK (hGQ hp.2))]
  exact (ParameterDeformation.value_mixed_parameter_eq_of_germ
    ((hU (p.1,0) (hSW p.1 hp.1)).contDiffAt (hW.mem_nhds (hSW p.1 hp.1)))
    ⟨G p.2,hΩK (hGQ hp.2)⟩ _ (he p.1 hp.1 p.2 hp.2) N v).symm

end OAI.Analysis.PDE.Dirichlet.ParameterDeformation
