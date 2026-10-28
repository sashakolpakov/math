import OAI.Analysis.PDE.Elliptic.Boundary.Third.CompositionHolder
import OAI.Analysis.PDE.Elliptic.Boundary.Third.Tensor

/-! The complete third tensor, with a quantitative Hölder norm, under a
fixed nonlinear boundary chart. -/

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder

variable {I : Type*} [Fintype I] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ I

local instance composeTensorFirstGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance composeTensorFirstSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance composeTensorSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance composeTensorSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance composeTensorThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance composeTensorThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance composeTensorFieldGroup : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
local instance composeTensorFieldSpace : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
local instance composeTensorFieldSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance composeTensorFieldSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance composeTensorFieldThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
local instance composeTensorFieldThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance

theorem exists_trilinear_holder_of_coordinates {S : Set E} {α C : ℝ} (hα : 0 ≤ α)
    (hC : 0 ≤ C) (t : S → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (ht : Continuous t)
    (R : I → I → I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α)
    (hRn : ∀ i j k, ‖R i j k‖ ≤ C)
    (hRv : ∀ i j k (x : S), OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i j k) x =
      t x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)) :
    ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = t x) ∧ ‖P‖ ≤ (Fintype.card I : ℝ)^3*C := by
  let N := (Fintype.card I : ℝ)^3*C
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hn (x : S) : ‖t x‖ ≤ N := by
    apply trilinear_norm_le_of_coordinate_bound
    intro i j k
    rw [← hRv i j k x, ← Real.norm_eq_abs]
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le _ _).trans (hRn i j k)
  have hh (x y : S) : ‖t x-t y‖ ≤ N*dist x y^α := by
    calc
      _ ≤ (Fintype.card I : ℝ)^3*(C*dist x y^α) := by
        apply trilinear_norm_le_of_coordinate_bound
        intro i j k
        simp only [sub_apply]
        rw [← hRv i j k x, ← hRv i j k y, ← Real.norm_eq_abs]
        exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le _ _ _).trans
          (mul_le_mul_of_nonneg_right (hRn i j k) (Real.rpow_nonneg dist_nonneg α))
      _ = N*dist x y^α := by dsimp only [N]; ring
  let P : S →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) :=
    BoundedContinuousFunction.ofNormedAddCommGroup t ht N hn
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα P hh, fun _ => rfl, ?_⟩
  exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα P hN hh).trans
    (max_le (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hN hn) le_rfl)

theorem third_composition_bound_nonneg {a b c d e f : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f) :
    0 ≤ 8*c*d^3 + 12*b*e*d + 2*a*f := by positivity

theorem third_chain_linear_bound {d D H T J K L A B R S : ℝ}
    (hd : 0 ≤ d) (hJ : 0 ≤ J) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hD : D ≤ A*R) (hH : H ≤ B*R) (hT : T ≤ B*S) :
    d*(8*T*J^3+12*H*K*J+2*D*L) ≤
      (d*(8*B*J^3+12*B*K*J+2*A*L)+1)*(R+S) := by
  calc
    _ ≤ d*(8*(B*(R+S))*J^3+12*(B*(R+S))*K*J+2*(A*(R+S))*L) := by
      gcongr
      · exact hT.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
      · exact hH.trans (mul_le_mul_of_nonneg_left (by linarith) hB)
      · exact hD.trans (mul_le_mul_of_nonneg_left (by linarith) hA)
    _ ≤ _ := by nlinarith

omit [DecidableEq I] in
theorem continuous_third_composition {u : E → ℝ} {G : E → E}
    (hu : ContDiff ℝ 3 u) (hG : ContDiff ℝ 3 G) :
    Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y))))) := by
  have h₁ : ContDiff ℝ 2 (fderiv ℝ (fun y => u (G y))) := (hu.comp hG).fderiv_right (by norm_num)
  have h₂ : ContDiff ℝ 1 (fderiv ℝ (fderiv ℝ (fun y => u (G y)))) := h₁.fderiv_right (by norm_num)
  exact h₂.continuous_fderiv one_ne_zero

def thirdBasisComponent {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α) (i j k : I) : OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α :=
  holderThirdComposeComponent (X := S) («E» := E) hα D H T J K L
    (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)

theorem thirdBasisComponent_norm {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α) (i j k : I) :
    ‖thirdBasisComponent hα D H T J K L i j k‖ ≤
      8*‖T‖*‖J‖^3+12*‖H‖*‖K‖*‖J‖+2*‖D‖*‖L‖ :=
  holderThirdComposeComponent_norm_le (X := S) («E» := E) hα D H T J K L
    (by simp) (by simp) (by simp)

theorem thirdBasisComponent_value {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α) (i j k : I) (x : S) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (thirdBasisComponent hα D H T J K L i j k) x =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value T x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (EuclideanSpace.single i 1))
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (EuclideanSpace.single j 1)) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (EuclideanSpace.single k 1)) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1))
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (EuclideanSpace.single k 1)) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (EuclideanSpace.single j 1))
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x (EuclideanSpace.single i 1) (EuclideanSpace.single k 1)) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x (EuclideanSpace.single i 1))
        (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value D x (OAI.Analysis.Normed.Function.Holder.HolderMap.value L x (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) (EuclideanSpace.single k 1)) := rfl

theorem exists_third_holder_of_chain_formula {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    (t : S → E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (ht : Continuous t)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (heq : ∀ (x : S) (q v w : E), t x q v w =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value T x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x q) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x q v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x v) (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x q w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value H x (OAI.Analysis.Normed.Function.Holder.HolderMap.value J x q) (OAI.Analysis.Normed.Function.Holder.HolderMap.value K x v w) +
      OAI.Analysis.Normed.Function.Holder.HolderMap.value D x (OAI.Analysis.Normed.Function.Holder.HolderMap.value L x q v w)) :
    ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = t x) ∧
      ‖P‖ ≤ (Fintype.card I : ℝ)^3 *
        (8*‖T‖*‖J‖^3 + 12*‖H‖*‖K‖*‖J‖ + 2*‖D‖*‖L‖) := by
  let C := 8*‖T‖*‖J‖^3 + 12*‖H‖*‖K‖*‖J‖ + 2*‖D‖*‖L‖
  have hC : 0 ≤ C := third_composition_bound_nonneg
    (norm_nonneg D) (norm_nonneg H) (norm_nonneg T) (norm_nonneg J) (norm_nonneg K) (norm_nonneg L)
  let R : I → I → I → OAI.Analysis.Normed.Function.Holder.HolderMap S ℝ α := thirdBasisComponent hα D H T J K L
  have hRn (i j k : I) : ‖R i j k‖ ≤ C :=
    thirdBasisComponent_norm hα D H T J K L i j k
  have hRv (i j k : I) (x : S) : OAI.Analysis.Normed.Function.Holder.HolderMap.value (R i j k) x =
      t x
        (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) (EuclideanSpace.single k 1) := by
    exact (thirdBasisComponent_value hα D H T J K L i j k x).trans
      (heq x _ _ _).symm
  exact exists_trilinear_holder_of_coordinates (I := I) hα hC t ht R hRn hRv

theorem exists_composed_third_holder {S : Set E} {α : ℝ} (hα : 0 ≤ α)
    {u : E → ℝ} {G : E → E} (hu : ContDiff ℝ 3 u) (hG : ContDiff ℝ 3 G)
    (D : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] ℝ) α)
    (H : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] ℝ) α)
    (T : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α)
    (J : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E) α)
    (K : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E) α)
    (L : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) α)
    (hD : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value D x = fderiv ℝ u (G x))
    (hH : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value H x = fderiv ℝ (fderiv ℝ u) (G x))
    (hT : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value T x = fderiv ℝ (fderiv ℝ (fderiv ℝ u)) (G x))
    (hJ : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value J x = fderiv ℝ G x)
    (hK : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value K x = fderiv ℝ (fderiv ℝ G) x)
    (hL : ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value L x = fderiv ℝ (fderiv ℝ (fderiv ℝ G)) x) :
    ∃ P : OAI.Analysis.Normed.Function.Holder.HolderMap S (E →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) α,
      (∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x =
        fderiv ℝ (fderiv ℝ (fderiv ℝ (fun y => u (G y)))) x) ∧
      ‖P‖ ≤ (Fintype.card I : ℝ)^3 *
        (8*‖T‖*‖J‖^3 + 12*‖H‖*‖K‖*‖J‖ + 2*‖D‖*‖L‖) := by
  apply exists_third_holder_of_chain_formula hα _
    ((continuous_third_composition hu hG).comp continuous_subtype_val) D H T J K L
  intro x q v w
  rw [hD, hH, hT, hJ, hK, hL]
  exact third_fderiv_comp hu.contDiffAt hG.contDiffAt q v w

end OAI.Analysis.PDE.Elliptic
