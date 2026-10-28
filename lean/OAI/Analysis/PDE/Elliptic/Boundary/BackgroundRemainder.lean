import OAI.Analysis.PDE.Elliptic.Boundary.FlatRemainder
import OAI.Analysis.PDE.Elliptic.Boundary.Curvature

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open Set InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem hessianOperator_sub {u B : E → ℝ} (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B) (x : E) :
    fderiv ℝ (gradient (fun y => u y - B y)) x =
      fderiv ℝ (gradient u) x - fderiv ℝ (gradient B) x := by
  have hgrad : gradient (fun y => u y - B y) = fun y => gradient u y - gradient B y := by
    funext y
    simpa only [neg_one_smul, sub_eq_add_neg] using gradient_add_smul
      (hu.differentiable (by norm_num)) (hB.differentiable (by norm_num)) (-1) y
  rw [hgrad]
  exact ((differentiable_gradient hu x).hasFDerivAt.sub (differentiable_gradient hB x).hasFDerivAt).fderiv

theorem exists_compact_hessian_lipschitz {B : E → ℝ} (hB : ContDiff ℝ 3 B)
    {K : Set E} (hK : IsCompact K) (hconv : Convex ℝ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ y ∈ K,
      ‖fderiv ℝ (gradient B) x - fderiv ℝ (gradient B) y‖ ≤ C * ‖x - y‖ := by
  have hc : Continuous (fun x => ‖iteratedFDeriv ℝ 3 B x‖) :=
    continuous_iff_continuousAt.mpr fun x => (hB.contDiffAt.continuousAt_iteratedFDeriv (by norm_num)).norm
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x hx y hy
  apply hessianOperator_lipschitz hB hconv _ hx hy
  intro z hz
  exact (by simpa using hC z hz : ‖iteratedFDeriv ℝ 3 B z‖ ≤ C).trans (le_max_right _ _)

theorem flat_hessian_remainder_with_background {u B : E → ℝ}
    (hu : ContDiff ℝ 2 u) (hB : ContDiff ℝ 2 B)
    {v z z' : E} (hv : ‖v‖ = 1) (hz : ‖z‖ < 1) (hz' : ‖z'‖ < 1)
    (hvz : inner ℝ v z = 0) (hvz' : inner ℝ v z' = 0)
    (hzero : ∀ y, ‖y‖ ≤ 1 → inner ℝ v y = 0 → u y = B y)
    {M Err : ℝ} (hM : 0 ≤ M)
    (hm : ∀ e, ‖e‖ ≤ 1 → inner ℝ v e = 0 →
      |fderiv ℝ (fderiv ℝ (fun y => u y - B y)) z v e -
        fderiv ℝ (fderiv ℝ (fun y => u y - B y)) z' v e| ≤ M)
    (hBdiff : ‖fderiv ℝ (gradient B) z - fderiv ℝ (gradient B) z'‖ ≤ Err) :
    ∃ t : ℝ, ‖(fderiv ℝ (gradient u) z - fderiv ℝ (gradient u) z') -
      t • rankOne ℝ v v‖ ≤ 4 * M + Err := by
  let H := fderiv ℝ (gradient (fun y => u y - B y)) z -
    fderiv ℝ (gradient (fun y => u y - B y)) z'
  let t := inner ℝ (H v) v
  have hrem : ‖H - t • rankOne ℝ v v‖ ≤ 4 * M :=
    flat_hessian_remainder_bound (hu.sub hB) hv hz hz' hvz hvz'
      (fun y hy hyv => sub_eq_zero.mpr (hzero y hy hyv)) hM hm
  have hid : (fderiv ℝ (gradient u) z - fderiv ℝ (gradient u) z') - t • rankOne ℝ v v =
      (H - t • rankOne ℝ v v) + (fderiv ℝ (gradient B) z - fderiv ℝ (gradient B) z') := by
    dsimp only [H]
    rw [hessianOperator_sub hu hB, hessianOperator_sub hu hB]
    abel
  refine ⟨t, ?_⟩
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add hrem hBdiff)

end OAI.Analysis.PDE.Elliptic
