import OAI.Analysis.Normed.Function.Holder.C2HolderOperator

noncomputable section
open Set
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Normed.Function.Holder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

local instance banachJetFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance banachJetFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance banachJetSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance banachJetSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

variable {Ω K : Set E} {α : ℝ} {hΩK : Ω ⊆ K}

def banachJetFunction (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) : E → ℝ :=
  OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)

theorem banachJetFunction_contDiffOn (hΩ : IsOpen Ω) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α) :
    ContDiffOn ℝ 2 (banachJetFunction U) Ω := OAI.Analysis.Normed.Function.Holder.C2Holder.contDiffOn_value hΩ U

theorem banachJetFunction_hessian_holder (hΩ : IsOpen Ω) (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := ℝ) hΩK α)
    (x : E) (hx : x ∈ Ω) (y : E) (hy : y ∈ Ω) :
    ‖fderiv ℝ (fderiv ℝ (banachJetFunction U)) x -
      fderiv ℝ (fderiv ℝ (banachJetFunction U)) y‖ ≤ ‖U‖ * ‖x - y‖ ^ α := by
  unfold banachJetFunction
  rw [(OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ U hx).2, (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ U hy).2]
  simpa only [Subtype.dist_eq, dist_eq_norm] using!
    OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative_holder U ⟨x, hΩK hx⟩ ⟨y, hΩK hy⟩

end OAI.Analysis.PDE.Nonlinear
