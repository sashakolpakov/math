import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Truncation
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Poisson

/-! The radially truncated Newtonian Hessian still has zero mean on every centered ball. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BigOperators
namespace OAI.Analysis.PDE.Schauder

theorem radialCutoff_eq_of_norm_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (r : ℝ) {x y : E} (h : ‖x‖ = ‖y‖) : radialCutoff r x = radialCutoff r y := by
  simp only [radialCutoff, norm_smul, h]

theorem truncatedNewtonianEntry_coordinate {m : ℕ} (i j : Fin m) {r : ℝ} (hr : 0 < r)
    (y : EuclideanSpace ℝ (Fin m)) :
    truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r y =
      (1 - radialCutoff r y) * ((2 - (m : ℝ)) * ‖y‖ ^ (-(m : ℝ)) * (if i = j then 1 else 0) +
        (m : ℝ) * (m - 2) * ‖y‖ ^ (-(m : ℝ) - 2) * y i * y j) := by
  by_cases hy : y = 0
  · subst y
    simp [truncatedNewtonianEntry,
      radialCutoff_one hr (by simpa using hr.le : ‖(0 : EuclideanSpace ℝ (Fin m))‖ ≤ r)]
  · rw [truncatedNewtonianEntry, newtonianEntry_coordinate i j y hy]

theorem truncatedNewtonianEntry_ball_offDiagonal {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) r y) = 0 := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrRight 2 fun k =>
      if k = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ
  let K := truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = -y i := by simp [e]
  have hej (y : EuclideanSpace ℝ (Fin m)) : e y j = y j := by simp [e, Ne.symm hij]
  have hK (y : EuclideanSpace ℝ (Fin m)) : K (e y) = -K y := by
    dsimp [K]
    rw [truncatedNewtonianEntry_coordinate i j hr, truncatedNewtonianEntry_coordinate i j hr,
      radialCutoff_eq_of_norm_eq r (e.norm_map y), e.norm_map, hei, hej, ite_eq_right hij]
    ring
  have he := MeasureTheory.integral_comp e ((ball 0 R).indicator K)
  have heq : (fun y => (ball 0 R).indicator K (e y)) = fun y => -((ball 0 R).indicator K y) := by
    funext y
    by_cases hy : ‖y‖ < R <;> simp [Set.indicator, e.norm_map, hy, hK]
  rw [heq, integral_neg, integral_indicator measurableSet_ball] at he
  change (∫ y in ball 0 R, K y) = 0
  linarith

theorem truncatedNewtonianEntry_ball_diag_eq {m : ℕ} (i j : Fin m) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) r y) =
    ∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) r y := by
  let e : EuclideanSpace ℝ (Fin m) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap i j)
  let K (i : Fin m) := truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) r
  have hei (y : EuclideanSpace ℝ (Fin m)) : e y i = y j := by
    simp [e, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  have hK (y : EuclideanSpace ℝ (Fin m)) : K i (e y) = K j y := by
    dsimp [K]
    rw [truncatedNewtonianEntry_coordinate i i hr, truncatedNewtonianEntry_coordinate j j hr,
      radialCutoff_eq_of_norm_eq r (e.norm_map y), e.norm_map, hei]
    simp only [ite_true]
  have he := MeasureTheory.integral_comp e ((ball 0 R).indicator (K i))
  have heq : (fun y => (ball 0 R).indicator (K i) (e y)) = (ball 0 R).indicator (K j) := by
    funext y
    by_cases hy : ‖y‖ < R <;> simp [Set.indicator, e.norm_map, hy, hK]
  rw [heq, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball] at he
  exact he.symm

theorem truncatedNewtonianEntry_ball {m : ℕ} (i j : Fin m) {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in ball 0 R, truncatedNewtonianEntry m (EuclideanSpace.single i (1 : ℝ))
      (EuclideanSpace.single j (1 : ℝ)) r y) = 0 := by
  by_cases hij : i = j
  · subst j
    let K (j : Fin m) := truncatedNewtonianEntry m (EuclideanSpace.single j (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) r
    have hi (j : Fin m) : IntegrableOn (K j) (ball 0 R) :=
      integrableOn_continuous_ball _ (contDiff_truncatedNewtonianEntry m _ _ hr).continuous R
    have htrace (y : EuclideanSpace ℝ (Fin m)) : ∑ j, K j y = 0 := by
      by_cases hy : y = 0
      · subst y
        simp [K, truncatedNewtonianEntry,
          radialCutoff_one hr (by simpa using hr.le : ‖(0 : EuclideanSpace ℝ (Fin m))‖ ≤ r)]
      · dsimp [K, truncatedNewtonianEntry]
        rw [← Finset.mul_sum, newtonianEntry_trace hy, mul_zero]
    have hsum : (m : ℝ) * (∫ y in ball 0 R, K i y) = 0 := by
      calc
        _ = ∑ j : Fin m, ∫ y in ball 0 R, K j y := by
          dsimp [K]
          simp_rw [truncatedNewtonianEntry_ball_diag_eq _ i hr R]
          simp
        _ = ∫ y in ball 0 R, ∑ j : Fin m, K j y :=
          (MeasureTheory.integral_finsetSum Finset.univ fun j _ => hi j).symm
        _ = 0 := by simp [htrace]
    exact (mul_eq_zero.mp hsum).resolve_left (by exact_mod_cast (show m ≠ 0 by have := i.isLt; omega))
  · exact truncatedNewtonianEntry_ball_offDiagonal i j hij hr R

end OAI.Analysis.PDE.Schauder
