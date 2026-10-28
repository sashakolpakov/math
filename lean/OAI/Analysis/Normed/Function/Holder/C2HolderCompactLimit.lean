import OAI.Analysis.Normed.Function.Holder.C2HolderOperator
import OAI.Analysis.Normed.Function.Holder.Banach.Cauchy

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

/-- Lower the Hölder exponent without changing the function or either
of its genuine derivative fields. -/
def lowerHalf (hα : 0 ≤ α) (u : C2Holder (F := F) hΩK α) :
    C2Holder (F := F) hΩK (α / 2) :=
  ⟨(u.val.1, u.val.2.1, OAI.Analysis.Normed.Function.Holder.HolderMap.lowerHalf hα u.val.2.2), u.property⟩

@[simp] theorem value_lowerHalf (hα : 0 ≤ α) (u : C2Holder (F := F) hΩK α) :
    C2Holder.value (C2Holder.lowerHalf hα u) = C2Holder.value u := rfl

@[simp] theorem firstDerivative_lowerHalf (hα : 0 ≤ α) (u : C2Holder (F := F) hΩK α) :
    C2Holder.firstDerivative (C2Holder.lowerHalf hα u) = C2Holder.firstDerivative u := rfl

@[simp] theorem secondDerivative_lowerHalf (hα : 0 ≤ α) (u : C2Holder (F := F) hΩK α) :
    C2Holder.secondDerivative (C2Holder.lowerHalf hα u) = C2Holder.secondDerivative u := rfl

theorem norm_lowerHalf_le_twice (hα : 0 ≤ α) (u : C2Holder (F := F) hΩK α) :
    ‖C2Holder.lowerHalf hα u‖ ≤ 2 * ‖u‖ := by
  change max ‖u.val.1‖ (max ‖u.val.2.1‖ ‖OAI.Analysis.Normed.Function.Holder.HolderMap.lowerHalf hα u.val.2.2‖) ≤ _
  refine max_le ?_ (max_le ?_ ?_)
  · exact (C2Holder.norm_value_le u).trans (by linarith [norm_nonneg u])
  · exact (C2Holder.norm_firstDerivative_le u).trans (by linarith [norm_nonneg u])
  · exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_lowerHalf_le_twice hα u.val.2.2).trans
      (mul_le_mul_of_nonneg_left (C2Holder.norm_hessianCLM_apply_le u) (by norm_num))

theorem norm_lowerHalf_limit_le (hα : 0 ≤ α)
    {f : ℕ → C2Holder (F := F) hΩK α} {g : C2Holder (F := F) hΩK (α / 2)}
    {M : ℝ} (hf : ∀ n, ‖f n‖ ≤ M)
    (hlim : Tendsto (fun n ↦ C2Holder.lowerHalf hα (f n)) atTop (𝓝 g)) : ‖g‖ ≤ 2 * M := by
  exact le_of_tendsto hlim.norm (Eventually.of_forall (fun n ↦
    (C2Holder.norm_lowerHalf_le_twice hα (f n)).trans
      (mul_le_mul_of_nonneg_left (hf n) (by norm_num))))

/-- A uniformly bounded C²,α sequence whose three jets are uniformly
Cauchy converges in C²,α/2. Closedness of the derivative graph ensures
that the limiting fields really are derivatives of the limiting value. -/
theorem exists_lowerHalf_limit [CompleteSpace F]
    (hΩ : IsOpen Ω) (hα : 0 ≤ α) (f : ℕ → C2Holder (F := F) hΩK α)
    {M : ℝ} (hM : 0 ≤ M) (hf : ∀ n, ‖f n‖ ≤ M)
    (hv : CauchySeq (fun n ↦ C2Holder.value (f n)))
    (hG : CauchySeq (fun n ↦ C2Holder.firstDerivative (f n)))
    (hH : CauchySeq (fun n ↦ C2Holder.secondDerivative (f n))) :
    ∃ g : C2Holder (F := F) hΩK (α / 2),
      Tendsto (fun n ↦ C2Holder.lowerHalf hα (f n)) atTop (𝓝 g) := by
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hv
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hG
  have hH' : CauchySeq (fun n ↦ OAI.Analysis.Normed.Function.Holder.HolderMap.lowerHalf hα (f n).val.2.2) :=
    OAI.Analysis.Normed.Function.Holder.HolderMap.cauchySeq_lowerHalf hα (fun n ↦ (f n).val.2.2) hM
      (fun n ↦ (C2Holder.norm_hessianCLM_apply_le (f n)).trans (hf n)) hH
  obtain ⟨H, hH⟩ := cauchySeq_tendsto_of_complete hH'
  have ht : Tendsto (fun n ↦ (C2Holder.lowerHalf hα (f n)).val) atTop
      (𝓝 (v, G, H)) := hv.prodMk_nhds (hG.prodMk_nhds hH)
  have hg : (v, G, H) ∈ secondJetGraph (F := F) hΩK (α / 2) :=
    (isClosed_secondJetGraph hΩ hΩK (α / 2)).mem_of_tendsto ht
      (Eventually.of_forall (fun n ↦ (C2Holder.lowerHalf hα (f n)).property))
  refine ⟨⟨(v, G, H), hg⟩, ?_⟩
  exact tendsto_subtype_rng.mpr ht

end OAI.Analysis.Normed.Function.Holder.C2Holder
