import OAI.Analysis.Normed.Function.Holder.Banach.Norm
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! Norm-preserving Hölder extension from a closed convex half-chart.
The nonexpansive retraction is constructed from the Hilbert projection
theorem, so the extension applies equally to scalar and matrix fields. -/

noncomputable section
open Set InnerProductSpace
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_nonexpansive_convex_retraction {K : Set E}
    (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K) :
    ∃ p : E → K, LipschitzWith 1 p ∧ ∀ x : K, p x = x := by
  choose p hp hmin using exists_norm_eq_iInf_of_complete_convex hne hc hconv
  have hchar (x : E) : ∀ y ∈ K, inner ℝ (x-p x) (y-p x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hconv (hp x)).mp (hmin x)
  have hdist (x y : E) : ‖p x-p y‖ ≤ ‖x-y‖ := by
    let d := p x-p y
    have hx := hchar x (p y) (hp y)
    have hy := hchar y (p x) (hp x)
    have hx' : 0 ≤ inner ℝ (x-p x) d := by
      have hd : p y-p x = -d := by dsimp only [d]; abel
      rw [hd, inner_neg_right] at hx
      linarith
    have hy' : inner ℝ (y-p y) d ≤ 0 := hy
    have hid : (x-p x)-(y-p y) = (x-y)-d := by dsimp only [d]; abel
    have hh : ‖d‖^2 ≤ inner ℝ (x-y) d := by
      have hh : 0 ≤ inner ℝ ((x-p x)-(y-p y)) d := by
        rw [inner_sub_left]
        linarith
      rw [hid, inner_sub_left, real_inner_self_eq_norm_sq] at hh
      linarith
    have hCS := real_inner_le_norm (x-y) d
    by_cases hd : ‖d‖ = 0
    · simpa only [d, hd] using norm_nonneg (x-y)
    · have hdp : 0 < ‖d‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
      apply (mul_le_mul_iff_right₀ hdp).mp
      nlinarith
  have hfix (x : K) : p x = (x : E) := by
    have h := hchar x x x.property
    rw [real_inner_self_eq_norm_sq] at h
    have hn : ‖(x:E)-p x‖ = 0 := by nlinarith [norm_nonneg ((x:E)-p x)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm
  refine ⟨fun x => ⟨p x, hp x⟩, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [Subtype.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] using hdist x y
  · intro x
    exact Subtype.ext (hfix x)

/-- Any bounded C^α field on a nonempty complete convex Hilbert subset
has a global C^α extension with no increase in the Hölder norm. -/
theorem exists_convex_holder_extension {K : Set E}
    (hne : K.Nonempty) (hc : IsComplete K) (hconv : Convex ℝ K)
    {α : ℝ} (hα : 0 ≤ α) (f : OAI.Analysis.Normed.Function.Holder.HolderMap K F α) :
    ∃ g : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
      (∀ x : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value g x = OAI.Analysis.Normed.Function.Holder.HolderMap.value f x) ∧ ‖g‖ ≤ ‖f‖ := by
  obtain ⟨p, hp, hfix⟩ := exists_nonexpansive_convex_retraction hne hc hconv
  let v : E →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.value f (p x)) ((OAI.Analysis.Normed.Function.Holder.HolderMap.value f).continuous.comp hp.continuous)
    ‖f‖ (fun x => OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f (p x))
  have hv : ∀ x y, ‖v x-v y‖ ≤ ‖f‖*(dist x y)^α := by
    intro x y
    apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f (p x) (p y)).trans
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Real.rpow_le_rpow dist_nonneg (by simpa using hp.dist_le_mul x y) hα
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα v hv, ?_, ?_⟩
  · intro x
    change OAI.Analysis.Normed.Function.Holder.HolderMap.value f (p x) = OAI.Analysis.Normed.Function.Holder.HolderMap.value f x
    rw [hfix]
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα v (norm_nonneg f) hv).trans
    apply max_le
    · exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg f) _
    · exact le_rfl

end OAI.Analysis.PDE.Elliptic
