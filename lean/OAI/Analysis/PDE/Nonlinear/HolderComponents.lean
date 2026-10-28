import OAI.Analysis.PDE.Nonlinear.ThirdHolder

/-! Finite directional Hölder estimates control the full derivative tensor. -/

noncomputable section
open Set Metric
open scoped Topology ComplexOrder
namespace OAI.Analysis.PDE.Nonlinear

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet

local instance componentFirstGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance componentFirstSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance componentSecondGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance componentSecondSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance componentThirdGroup (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance componentThirdSpace (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

theorem clm_norm_le_sum_basis {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis I ℝ E) (L : E →L[ℝ] F) :
    ‖L‖ ≤ ∑ i, ‖L (b i)‖ := by
  classical
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have he : L x = ∑ i, inner ℝ (b i) x • L (b i) := by
    conv_lhs => rw [← b.sum_repr' x]
    simp only [map_sum, map_smul]
  rw [he]
  calc
    _ ≤ ∑ i, ‖inner ℝ (b i) x • L (b i)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖x‖ * ‖L (b i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      simpa only [b.norm_eq_one, one_mul] using norm_inner_le_norm (b i) x
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem locally_holder_of_basis_components {I E F X : Type*} [Fintype I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup X]
    (b : OrthonormalBasis I ℝ E) (f : X → E →L[ℝ] F) (x₀ : X) (α : ℝ)
    (h : ∀ i, ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖f x (b i) - f y (b i)‖ ≤ C * ‖x - y‖ ^ α) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α := by
  classical
  choose r hr C hC hh using h
  let s := Finset.univ.inf' Finset.univ_nonempty r
  have hs : 0 < s := (Finset.lt_inf'_iff Finset.univ_nonempty).mpr (fun i _ => hr i)
  have hsr (i) : s ≤ r i := Finset.inf'_le r (Finset.mem_univ i)
  refine ⟨s, hs, (∑ i, C i) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ i, C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    linarith only [this]
  · intro x hx y hy
    calc
      _ ≤ ∑ i, ‖(f x - f y) (b i)‖ := clm_norm_le_sum_basis b (f x - f y)
      _ ≤ ∑ i, C i * ‖x - y‖ ^ α := by
        apply Finset.sum_le_sum
        intro i hi
        exact hh i x (ball_subset_ball (hsr i) hx) y (ball_subset_ball (hsr i) hy)
      _ = (∑ i, C i) * ‖x - y‖ ^ α := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)

theorem third_derivative_directional_hessian {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : ContDiff ℝ 3 u) (x v : E) :
    fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x v = fderiv ℝ (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u v)) x := by
  ext i j
  have he : OAI.Analysis.PDE.Dirichlet.directionalDerivative (OAI.Analysis.PDE.Dirichlet.directionalDerivative u j) i =
      fun y => fderiv ℝ (fderiv ℝ u) y i j := by
    funext y
    exact OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (hu.of_le (by norm_num)) i j y
  have ht := OAI.Analysis.PDE.Dirichlet.directionalDerivative_triple_comm hu v i j x
  rw [he, OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice (OAI.Analysis.PDE.Dirichlet.contDiff_directionalDerivative hu (by norm_num) v)] at ht
  change fderiv ℝ (fun y => fderiv ℝ (fderiv ℝ u) y i j) x v = _ at ht
  rwa [OAI.Analysis.Calculus.Quaternion.fderiv_second_apply hu.contDiffAt v i j] at ht

theorem moore_third_derivative_holder {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (hu : ContDiff ℝ 3 u) (hf : ContDiff ℝ 2 f) (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4)
    (hPDE : ∀ᶠ x in nhds x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in nhds x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
        C * ‖x - y‖ ^ α := by
  have hn0 : 0 < n := by omega
  let : NeZero n := ⟨by omega⟩
  apply locally_holder_of_basis_components (EuclideanSpace.basisFun (Fin n × Fin 4) ℝ)
    (fun x => fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x) x₀ α
  intro i
  obtain ⟨r, hr, C, hC, hh⟩ := moore_directional_hessian_holder hn hα hα1 u f hu hf
    (EuclideanSpace.basisFun (Fin n × Fin 4) ℝ i) x₀ hPDE hPD
  refine ⟨r, hr, C, hC, ?_⟩
  intro x hx y hy
  simpa only [third_derivative_directional_hessian u hu] using hh x hx y hy

theorem moore_third_derivative_holder_local {n : ℕ} (hn : 3 ≤ n * 4) {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) (u f : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4 → ℝ)
    (x₀ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n 4) (hu : ContDiffAt ℝ 3 u x₀) (hf : ContDiffAt ℝ 2 f x₀)
    (hPDE : ∀ᶠ x in nhds x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x) = f x)
    (hPD : ∀ᶠ x in nhds x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x)).PosDef) :
    ∃ r > 0, ∃ C > 0, ∀ x ∈ ball x₀ r, ∀ y ∈ ball x₀ r,
      ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x - fderiv ℝ (fderiv ℝ (fderiv ℝ u)) y‖ ≤
        C * ‖x - y‖ ^ α := by
  obtain ⟨g, hg, hgu⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hu
  obtain ⟨d, hd, hdf⟩ := OAI.Analysis.PDE.Dirichlet.exists_contDiff_extension_near_point hf
  have hHg : ∀ᶠ x in nhds x₀, OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x = OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    filter_upwards [hgu.eventuallyEq_nhds] with x hx
    exact OAI.Analysis.PDE.Dirichlet.quaternionHessian_congr_germ OAI.Analysis.Calculus.Quaternion.fourSlots hx
  have hp : ∀ᶠ x in nhds x₀, OAI.LinearAlgebra.Moore.mooreDet n (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x) = d x := by
    filter_upwards [hHg, hdf, hPDE] with x hx hy hz
    rw [hx, hz, hy]
  have hpos : ∀ᶠ x in nhds x₀, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots g x)).PosDef := by
    filter_upwards [hHg, hPD] with x hx hy
    rwa [hx]
  obtain ⟨r, hr, C, hC, hh⟩ := moore_third_derivative_holder hn hα hα1 g d hg hd x₀ hp hpos
  obtain ⟨s, hs, hsame⟩ := Metric.eventually_nhds_iff.mp
    (((hgu.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ))
  refine ⟨min r s, lt_min hr hs, C, hC, ?_⟩
  intro x hx y hy
  rw [← hsame (ball_subset_ball (min_le_right r s) hx),
    ← hsame (ball_subset_ball (min_le_right r s) hy)]
  exact hh x (ball_subset_ball (min_le_left r s) hx) y (ball_subset_ball (min_le_left r s) hy)

end OAI.Analysis.PDE.Nonlinear
