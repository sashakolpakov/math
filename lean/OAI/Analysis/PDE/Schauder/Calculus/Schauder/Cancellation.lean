import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Annulus

/-! Exact cancellation of the actual Newtonian Hessian on concentric annuli. -/

noncomputable section
open _root_.MeasureTheory Set Metric
open scoped BigOperators
namespace OAI.Analysis.PDE.Schauder

theorem newtonianEntry_coordinate {m : ℕ} (i j : Fin m)
    (y : EuclideanSpace ℝ (Fin m)) (hy : y ≠ 0) :
    newtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y =
      (2 - (m : ℝ)) * ‖y‖ ^ (-(m : ℝ)) * (if i = j then 1 else 0) +
        (m : ℝ) * (m - 2) * ‖y‖ ^ (-(m : ℝ) - 2) * y i * y j := by
  rw [newtonianEntry_formula m _ _ hy]
  by_cases hij : i = j
  · subst j
    simp [EuclideanSpace.inner_single_right]
  · simp [EuclideanSpace.inner_single_right, hij, Ne.symm hij]

theorem integrableOn_newtonianEntry_annulus {m : ℕ} (v w : EuclideanSpace ℝ (Fin m))
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    IntegrableOn (newtonianEntry m v w) (normAnnulus r R) :=
  integrableOn_normAnnulus _ (fun _ hy => (contDiffAt_newtonianEntry m v w hy).continuousAt) hr R

theorem newtonianEntry_annulus_offDiagonal {m : ℕ} (i j : Fin m) (hij : i ≠ j)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in normAnnulus r R,
      newtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) = 0 := by
  calc
    _ = ∫ y in normAnnulus r R, (m : ℝ) * (m - 2) *
        (‖y‖ ^ (-(m : ℝ) - 2) * (y : EuclideanSpace ℝ (Fin m)) i * y j) := by
      apply setIntegral_congr_fun (measurableSet_normAnnulus r R)
      intro y hy
      rw [newtonianEntry_coordinate i j y (norm_pos_iff.mp (hr.trans hy.1))]
      simp only [ite_eq_right hij, mul_zero, zero_add]
      ring
    _ = 0 := by rw [integral_const_mul, annularMoment_offDiagonal _ r R i j hij, mul_zero]

theorem newtonianEntry_annulus_diagonal {m : ℕ} (i : Fin m)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in normAnnulus r R,
      newtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) y) = 0 := by
  have hpow : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) => ‖y‖ ^ (-(m : ℝ)))
      (normAnnulus r R) :=
    integrableOn_normAnnulus _ (fun y hy =>
      continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hy))) hr R
  have hmom : IntegrableOn (fun y : EuclideanSpace ℝ (Fin m) =>
      ‖y‖ ^ (-(m : ℝ) - 2) * y i * y i) (normAnnulus r R) :=
    integrableOn_normAnnulus _ (fun y hy =>
      ((continuous_norm.continuousAt.rpow_const (Or.inl (norm_ne_zero_iff.mpr hy))).mul
        (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).continuousAt).mul
          (PiLp.continuous_apply 2 (fun _ : Fin m => ℝ) i).continuousAt) hr R
  have htrace := annularMoment_trace (-(m : ℝ) - 2) hr R i
  have he : (∫ y in normAnnulus r R, (‖y‖ : ℝ) ^ (-(m : ℝ) - 2) *
      ‖(y : EuclideanSpace ℝ (Fin m))‖ ^ 2) =
        ∫ y in normAnnulus r R, ‖(y : EuclideanSpace ℝ (Fin m))‖ ^ (-(m : ℝ)) := by
    apply setIntegral_congr_fun (measurableSet_normAnnulus r R)
    intro y hy
    dsimp only
    rw [← Real.rpow_natCast, ← Real.rpow_add (hr.trans hy.1)]
    congr 1
    norm_num
  rw [he] at htrace
  calc
    _ = ∫ y in normAnnulus r R,
        (2 - (m : ℝ)) * ‖(y : EuclideanSpace ℝ (Fin m))‖ ^ (-(m : ℝ)) +
          (m : ℝ) * (m - 2) * (‖y‖ ^ (-(m : ℝ) - 2) * y i * y i) := by
      apply setIntegral_congr_fun (measurableSet_normAnnulus r R)
      intro y hy
      rw [newtonianEntry_coordinate i i y (norm_pos_iff.mp (hr.trans hy.1))]
      simp only [ite_true, mul_one]
      ring
    _ = _ := by
      rw [integral_add (hpow.const_mul _) (hmom.const_mul _), integral_const_mul,
        integral_const_mul, ← htrace]
      ring

theorem newtonianEntry_annulus_coordinate {m : ℕ} (i j : Fin m)
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in normAnnulus r R,
      newtonianEntry m (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) y) = 0 := by
  by_cases hij : i = j
  · subst j; exact newtonianEntry_annulus_diagonal i hr R
  · exact newtonianEntry_annulus_offDiagonal i j hij hr R

theorem newtonianEntry_basis_expansion {m : ℕ} (v w y : EuclideanSpace ℝ (Fin m)) :
    newtonianEntry m v w y = ∑ i : Fin m, ∑ j : Fin m,
      (v i * w j) * newtonianEntry m (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) y := by
  have hv : (∑ i : Fin m, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  have hw : (∑ j : Fin m, w j • EuclideanSpace.single j (1 : ℝ)) = w := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr w
  change newtonianSecond m y v w = _
  calc
    _ = newtonianSecond m y (∑ i : Fin m, v i • EuclideanSpace.single i (1 : ℝ))
        (∑ j : Fin m, w j • EuclideanSpace.single j (1 : ℝ)) := by rw [hv, hw]
    _ = _ := by
      simp only [map_sum, map_smul, sum_apply,
        smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc, newtonianEntry]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem newtonianEntry_annulus {m : ℕ} (v w : EuclideanSpace ℝ (Fin m))
    {r : ℝ} (hr : 0 < r) (R : ℝ) :
    (∫ y in normAnnulus r R, newtonianEntry m v w y) = 0 := by
  have hij (i j : Fin m) : IntegrableOn
      (fun y => (v i * w j) * newtonianEntry m (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) y) (normAnnulus r R) :=
    (integrableOn_newtonianEntry_annulus _ _ hr R).const_mul _
  have he : newtonianEntry m v w = fun y => ∑ i : Fin m, ∑ j : Fin m,
      (v i * w j) * newtonianEntry m (EuclideanSpace.single i (1 : ℝ))
        (EuclideanSpace.single j (1 : ℝ)) y :=
    funext (newtonianEntry_basis_expansion v w)
  rw [he]
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ =>
    MeasureTheory.integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  apply Finset.sum_eq_zero
  intro i hi
  rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hij i j)]
  apply Finset.sum_eq_zero
  intro j hj
  rw [integral_const_mul, newtonianEntry_annulus_coordinate i j hr R, mul_zero]

end OAI.Analysis.PDE.Schauder
