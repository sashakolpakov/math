import OAI.Analysis.PDE.Dirichlet.Rough.Boundary.LocalTangents

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {r : E → ℝ} {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}

local instance curveTangentsFirstGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] ℝ) := inferInstance
local instance curveTangentsFirstSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] ℝ) := inferInstance
local instance curveTangentsSecondGroup (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedAddCommGroup (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance curveTangentsSecondSpace (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    NormedSpace ℝ (X →L[ℝ] X →L[ℝ] ℝ) := inferInstance
local instance curveTangentsHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance
local instance curveTangentsHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α) := inferInstance

omit [Nontrivial E] in
/-- Pointwise translation germs of the Banach-space solution curve already
give the closed-set tangential regularity needed by the nonlinear bootstrap. -/
theorem local_tangents_of_parameter_curves
    (hr : ContDiff ℝ 3 r) (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {S : Set V} {G : V → E} (hG : ContDiffOn ℝ 2 G S) (hGS : MapsTo G S {x | r x ≤ 0})
    {f : V → ℝ} (hf : ∀ z ∈ S, ContDiffAt ℝ 2 f z) (ℓ : V →L[ℝ] ℝ)
    (hcurves : ∀ v, ℓ v = 0 → ∃ O : Set V, IsOpen O ∧ (0 : V) ∈ O ∧
      ∃ U : ℝ → OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩD α, ContDiffAt ℝ 2 U 0 ∧
        ∀ z (hz : z ∈ S ∩ O),
          (fun t ↦ OAI.Analysis.Normed.Function.Holder.C2Holder.value (U t) ⟨G z,hGS hz.1⟩) =ᶠ[𝓝 0]
            fun t ↦ f (z + t • v)) :
    ∀ v, ℓ v = 0 → ∃ O : Set V, IsOpen O ∧ (0 : V) ∈ O ∧
      ContDiffOn ℝ 2 (constantDirectional f v) (S ∩ O) ∧
      ContDiffOn ℝ 2 (fun z ↦ fderiv ℝ (fderiv ℝ f) z v v) (S ∩ O) := by
  intro v hv
  obtain ⟨O,hO,hzero,U,hU,he⟩ := hcurves v hv
  refine ⟨O,hO,hzero,?_,?_⟩
  · exact first_tangent_contDiffOn_of_parameter_curve hr hreg
      (hU.differentiableAt (by norm_num)) (hG.mono inter_subset_left)
      (fun z hz ↦ hGS hz.1) v (fun z hz ↦ (hf z hz.1).differentiableAt (by norm_num)) he
  · exact diagonal_tangent_contDiffOn_of_parameter_curve hr hreg hU
      (hG.mono inter_subset_left) (fun z hz ↦ hGS hz.1) v (fun z hz ↦ hf z hz.1) he

/-- Adding back the smooth prescribed boundary extension does not demand
any extra regularity from the rough solution. -/
theorem tangent_regularities_add_smooth
    {S : Set V} {f b : V → ℝ} (hf : ∀ x ∈ S, ContDiffAt ℝ 2 f x)
    (hb : ContDiff ℝ 4 b) (v : V)
    (ht : ContDiffOn ℝ 2 (constantDirectional f v) S)
    (htt : ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ f) x v v) S) :
    ContDiffOn ℝ 2 (constantDirectional (fun x ↦ f x + b x) v) S ∧
      ContDiffOn ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ (fun y ↦ f y + b y)) x v v) S := by
  have hb1 : ContDiff ℝ 2 (constantDirectional b v) :=
    (hb.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const
  have hb2 : ContDiff ℝ 2 (fun x ↦ fderiv ℝ (fderiv ℝ b) x v v) :=
    (((hb.fderiv_right (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)).clm_apply
      contDiff_const).clm_apply contDiff_const
  constructor
  · apply (ht.add hb1.contDiffOn).congr
    intro x hx
    simp only [constantDirectional]
    change fderiv ℝ (f + b) x v = _
    rw [fderiv_add ((hf x hx).differentiableAt (by norm_num))
      (hb.differentiable (by norm_num) x)]
    rfl
  · apply (htt.add hb2.contDiffOn).congr
    intro x hx
    rw [OAI.Analysis.PDE.Schauder.second_fderiv_add_at (hf x hx) (hb.contDiffAt.of_le (by norm_num))]
    rfl

end OAI.Analysis.PDE.Dirichlet
