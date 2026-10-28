import OAI.Analysis.PDE.Elliptic.Boundary.CommutatorHolder

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {X E F : Type*} [MetricSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

local instance actionsFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance actionsFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance actionsSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance actionsSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance actionsThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance actionsThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance actionsFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance actionsFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance

def holderAction₂ (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] F) α)
    (a b : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) : OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (OAI.Analysis.Normed.Function.Holder.HolderMap.action hα A a) b

def holderAction₃ (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) α)
    (a b c : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) : OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (holderAction₂ hα A a b) c

def holderAction₄ (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) α)
    (a b c d : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) : OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  OAI.Analysis.Normed.Function.Holder.HolderMap.action hα (holderAction₃ hα A a b c) d

theorem holderAction_bound (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] F) α)
    (a : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) {R N : ℝ} (hR : 0 ≤ R) (_ : 0 ≤ N)
    (hA : ‖A‖ ≤ R) (ha : ‖a‖ ≤ N) : ‖OAI.Analysis.Normed.Function.Holder.HolderMap.action hα A a‖ ≤ 2*R*N := by
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα A a).trans (by gcongr)

theorem holderAction₂_bound (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] F) α)
    (a b : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) {R N : ℝ} (hR : 0 ≤ R) (hN : 0 ≤ N)
    (hA : ‖A‖ ≤ R) (ha : ‖a‖ ≤ N) (hb : ‖b‖ ≤ N) :
    ‖holderAction₂ hα A a b‖ ≤ (2*N)^2*R := by
  apply (holderAction_bound hα _ b (by positivity) hN
    (holderAction_bound hα A a hR hN hA ha) hb).trans
  exact le_of_eq (by ring)

theorem holderAction₃_bound (hα : 0 ≤ α) (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) α)
    (a b c : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) {R N : ℝ} (hR : 0 ≤ R) (hN : 0 ≤ N)
    (hA : ‖A‖ ≤ R) (ha : ‖a‖ ≤ N) (hb : ‖b‖ ≤ N) (hc : ‖c‖ ≤ N) :
    ‖holderAction₃ hα A a b c‖ ≤ (2*N)^3*R := by
  apply (holderAction_bound hα _ c (by positivity) hN
    (holderAction₂_bound hα A a b hR hN hA ha hb) hc).trans
  exact le_of_eq (by ring)

theorem holderAction₄_bound (hα : 0 ≤ α)
    (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) α)
    (a b c d : OAI.Analysis.Normed.Function.Holder.HolderMap X E α) {R N : ℝ} (hR : 0 ≤ R) (hN : 0 ≤ N)
    (hA : ‖A‖ ≤ R) (ha : ‖a‖ ≤ N) (hb : ‖b‖ ≤ N) (hc : ‖c‖ ≤ N) (hd : ‖d‖ ≤ N) :
    ‖holderAction₄ hα A a b c d‖ ≤ (2*N)^4*R := by
  apply (holderAction_bound hα _ d (by positivity) hN
    (holderAction₃_bound hα A a b c hR hN hA ha hb hc) hd).trans
  exact le_of_eq (by ring)

theorem holder_action_power_mono {N R : ℝ} (hN : 1 ≤ N) (hR : 0 ≤ R)
    {k : ℕ} (hk : k ≤ 4) : (2*N)^k*R ≤ (2*N)^4*R :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith : 1 ≤ 2*N) hk) hR

end OAI.Analysis.PDE.Elliptic
