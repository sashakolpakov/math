import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.CompositionHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Fourth.Tensor

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {E I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fintype I]

local instance fourthComposeTensor1Group : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor1Space : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance fourthComposeTensor4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

omit [FiniteDimensional ℝ E] in
theorem clm_norm_le_card_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : OrthonormalBasis I ℝ E) (A : E →L[ℝ] F) (M : ℝ)
    (h : ∀ i, ‖A (b i)‖ ≤ M) : ‖A‖ ≤ (Fintype.card I : ℝ)*M := by
  calc
    _ ≤ ∑ i, ‖A (b i)‖ := OAI.Analysis.PDE.Nonlinear.clm_norm_le_sum_basis b A
    _ ≤ ∑ _i : I, M := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp

omit [FiniteDimensional ℝ E] in
theorem quadrilinear_norm_le_of_coordinates
    (b : OrthonormalBasis I ℝ E) (A : E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (M : ℝ)
    (h : ∀ i j k l, ‖A (b i) (b j) (b k) (b l)‖ ≤ M) :
    ‖A‖ ≤ (Fintype.card I : ℝ)^4*M := by
  calc
    _ ≤ (Fintype.card I : ℝ)*((Fintype.card I : ℝ)*((Fintype.card I : ℝ)*((Fintype.card I : ℝ)*M))) :=
      clm_norm_le_card_mul b A _ (fun i =>
        clm_norm_le_card_mul b (A (b i)) _ (fun j =>
          clm_norm_le_card_mul b (A (b i) (b j)) _ (fun k =>
            clm_norm_le_card_mul b (A (b i) (b j) (b k)) M (h i j k))))
    _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- Coordinate Hölder fields determine the entire fourth-order tensor. -/
theorem exists_quadrilinear_holder_of_coordinates
    (b : OrthonormalBasis I ℝ E) {S : Set E} {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C)
    (t : S → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (ht : Continuous t)
    (R : I → I → I → I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (hRn : ∀ i j k l, ‖R i j k l‖ ≤ C)
    (hRv : ∀ i j k l (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i j k l) x = t x (b i) (b j) (b k) (b l)) :
    ∃ Q : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = t x) ∧ ‖Q‖ ≤ (Fintype.card I : ℝ)^4*C := by
  let N := (Fintype.card I : ℝ)^4*C
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hn (x : S) : ‖t x‖ ≤ N := by
    apply quadrilinear_norm_le_of_coordinates b
    intro i j k l
    rw [← hRv i j k l x]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans (hRn i j k l)
  have hh (x y : S) : ‖t x-t y‖ ≤ N*dist x y^α := by
    calc
      _ ≤ (Fintype.card I : ℝ)^4*(C*dist x y^α) := by
        apply quadrilinear_norm_le_of_coordinates b
        intro i j k l
        simp only [sub_apply]
        rw [← hRv i j k l x, ← hRv i j k l y]
        exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le _ _ _).trans
          (mul_le_mul_of_nonneg_right (hRn i j k l) (Real.rpow_nonneg dist_nonneg _))
      _ = N*dist x y^α := by dsimp only [N]; ring
  let Q₀ : S →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup t ht N hn
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα Q₀ hh, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα Q₀ hN hh).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le ht hN hn) le_rfl)


local instance fourthComposeMap1Group : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance fourthComposeMap1Space : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance fourthComposeMap2Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeMap2Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeMap3Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeMap3Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeMap4Group : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance fourthComposeMap4Space : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

omit [FiniteDimensional ℝ E] in
/-- Quantitative fourth-order coordinate transport, linear in the outer
jet bound; only the fixed chart contributes the fourth-power factor. -/
theorem exists_composed_fourth_holder
    (b : OrthonormalBasis I ℝ E) {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    {u : E → ℝ} {G : E → E} (hu : ContDiff ℝ 4 u) (hG : ContDiff ℝ 4 G)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (Q : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (V : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (hD : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u (G x))
    (hH : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) (G x))
    (hT : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (G x))
    (hQ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value Q x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ u))) (G x))
    (hJ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ G x)
    (hK : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ G) x)
    (hL : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value L x = fderiv ℝ (fderiv ℝ (fderiv ℝ G)) x)
    (hV : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value V x = fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ G))) x)
    {R N : ℝ} (hR : 0 ≤ R) (hN : 1 ≤ N)
    (hDn : ‖D‖ ≤ R) (hHn : ‖H‖ ≤ R) (hTn : ‖T‖ ≤ R) (hQn : ‖Q‖ ≤ R)
    (hJn : ‖J‖ ≤ N) (hKn : ‖K‖ ≤ N) (hLn : ‖L‖ ≤ N) (hVn : ‖V‖ ≤ N) :
    HasFourthHolderBound S α (fun y => u (G y)) ((Fintype.card I : ℝ)^4*(15*((2*N)^4*R))) := by
  have h₁ : ContDiff ℝ 3 (fderiv ℝ (fun y => u (G y))) := (hu.comp hG).fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ (fun y => u (G y)))) := h₁.fderiv_right (by norm_num)
  have h₃ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y))))) :=
    h₂.fderiv_right (by norm_num)
  apply exists_quadrilinear_holder_of_coordinates b hα (by positivity) _
    ((h₃.continuous_fderiv one_ne_zero).comp continuous_subtype_val)
    (fun i j k l => holderFourthComposeComponent hα D H T Q J K L V (b i) (b j) (b k) (b l))
  · intro i j k l
    exact holderFourthComposeComponent_bound hα D H T Q J K L V hR hN
      hDn hHn hTn hQn hJn hKn hLn hVn
      (b.norm_eq_one i).le (b.norm_eq_one j).le (b.norm_eq_one k).le (b.norm_eq_one l).le
  · intro i j k l x
    rw [value_holderFourthComposeComponent, hD, hH, hT, hQ, hJ, hK, hL, hV]
    exact (fourth_fderiv_comp hu.contDiffAt hG.contDiffAt (b i) (b j) (b k) (b l)).symm


end OAI.Analysis.PDE.Elliptic
