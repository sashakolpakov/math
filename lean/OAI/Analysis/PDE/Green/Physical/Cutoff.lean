import OAI.Analysis.PDE.Green.Physical.Coordinates

/-! A scale-independent cutoff integral bound for the actual physical fibers,
including the periodic real spatial variables. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Filter _root_.MeasureTheory OAI.Analysis.Calculus.Current
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}

def physicalBoxLower (c : (ι × Fin 3) ≃ Fin (m + 1)) (j : Fin (m + 1)) : ℝ :=
  if (c.symm j).2 = 0 then 0 else -29

def physicalBoxUpper (c : (ι × Fin 3) ≃ Fin (m + 1)) (j : Fin (m + 1)) : ℝ :=
  if (c.symm j).2 = 0 then 1 else 29

omit [Fintype ι] [DecidableEq ι] in
theorem physicalBoxLower_le_upper (c : (ι × Fin 3) ≃ Fin (m + 1)) :
    physicalBoxLower c ≤ physicalBoxUpper c := by
  intro j
  simp only [physicalBoxLower, physicalBoxUpper]
  split_ifs <;> norm_num

omit [DecidableEq ι] in
theorem physicalBox_compatible_faces (c : (ι × Fin 3) ≃ Fin (m + 1))
    (R : (ι → ℂ) → ℝ) (V : (ι → ℂ) → (ι → ℂ))
    (hbounded : ∀ q, R q ≤ 0 → ‖q‖ ≤ 28) :
    CompatibleBoxFaces (physicalBoxLower c) (physicalBoxUpper c)
      (R ∘ complexSpatialProjection c) (fun i x => liftedSpatialField c V x i) := by
  intro i y hy
  by_cases hi : (c.symm i).2 = 0
  · exact Or.inr (Or.inr ⟨liftedSpatialField_zero_real c V _ i hi,
      liftedSpatialField_zero_real c V _ i hi⟩)
  · apply Or.inr ∘ Or.inl
    constructor
    · by_contra hn
      have hb := hbounded _ (le_of_lt (lt_of_not_ge hn))
      have hc := abs_coordinate_le_complexProjection_norm c
        (i.insertNth (physicalBoxUpper c i) y) i hi
      simp only [Fin.insertNth_apply_same, physicalBoxUpper, ite_eq_right hi, Real.norm_eq_abs,
        abs_of_nonneg (show (0 : ℝ) ≤ 29 by norm_num)] at hc
      simp only [physicalBoxUpper, ite_eq_right hi] at hb
      linarith
    · by_contra hn
      have hb := hbounded _ (le_of_lt (lt_of_not_ge hn))
      have hc := abs_coordinate_le_complexProjection_norm c
        (i.insertNth (physicalBoxLower c i) y) i hi
      simp only [Fin.insertNth_apply_same, physicalBoxLower, ite_eq_right hi, Real.norm_eq_abs,
        abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 29 by norm_num)] at hc
      simp only [physicalBoxLower, ite_eq_right hi] at hb
      linarith

omit [DecidableEq ι] in
theorem physical_extension_cutoff_bound (c : (ι × Fin 3) ≃ Fin (m + 1))
    {R : (ι → ℂ) → ℝ} {V : (ι → ℂ) → (ι → ℂ)}
    (hR : ContDiff ℝ 3 R) (hV : ContDiff ℝ 3 V)
    {C S : ℝ} (hC : 0 ≤ C) (hS : ∀ t, ‖transitionSlope t‖ ≤ S)
    (hgeom : ∀ q, R q ≤ 0 →
      1 ≤ fderiv ℝ R q (V q) + (R q) ^ 2 ∧
      ‖fderiv ℝ V q‖ ≤ C ∧ ‖R q‖ ≤ 1 ∧ ‖q‖ ≤ 28)
    (k : ℕ) :
    (∫ x in Icc (physicalBoxLower c) (physicalBoxUpper c),
      normalCutoffWeight (R (complexSpatialProjection c x)) k) ≤
      ((m + 1 : ℝ) * (2 * C) + S) *
        boxVolume (physicalBoxLower c) (physicalBoxUpper c) := by
  have hW := contDiff_liftedSpatialField c hV
  have hR' : ContDiff ℝ 1 (R ∘ complexSpatialProjection c) :=
    (hR.of_le (by norm_num)).comp (complexSpatialProjection c).contDiff
  have hF : ∀ i, ContDiff ℝ 1 (fun x => liftedSpatialField c V x i) := fun i =>
    (ContinuousLinearMap.proj i : (Fin (m + 1) → ℝ) →L[ℝ] ℝ).contDiff.comp
      (hW.of_le (by norm_num))
  have hbound := normalCutoffWeight_integral_bound_on_sublevel
    (physicalBoxLower c) (physicalBoxUpper c) (physicalBoxLower_le_upper c)
    (fun i x => liftedSpatialField c V x i) hF hR'
    (c := 1) (C := S) (D := (m + 1 : ℝ) * (2 * C)) (R := 1)
    (by norm_num) hS (by positivity) (by norm_num) ?_ ?_ ?_
    (physicalBox_compatible_faces c R V (fun q hq => (hgeom q hq).2.2.2)) k
  · simpa only [mul_one, div_one, Function.comp_apply] using hbound
  · intro x hx hneg
    rw [liftedSpatialField_transverse c V x (hR.differentiable (by norm_num) _)]
    exact (hgeom _ (le_of_lt hneg)).1
  · intro x hx hneg
    have hd := vectorField_divergence_norm_le (hW.differentiable (by norm_num) x)
      (liftedSpatialField_derivative_norm_le c x (hV.differentiable (by norm_num) _)
        (hgeom _ (le_of_lt hneg)).2.1)
    simpa only [Nat.cast_add, Nat.cast_one] using hd
  · intro x hx hneg
    exact (hgeom _ (le_of_lt hneg)).2.2.1

/-- This is the uniform cutoff mass for the original rational defining function,
not an estimate assuming a geometric bound on its level sets. -/
theorem exists_uniform_physical_cutoff_bound (d : ℕ)
    (c : (Option (Fin d) × Fin 3) ≃ Fin (m + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (a : ℝ) (τ : ℂ), 0 < a → a ≤ ‖τ‖ → ‖τ‖ ≤ 4 →
      ∀ k : ℕ, (∫ x in Icc (physicalBoxLower c) (physicalBoxUpper c),
        normalCutoffWeight (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ
          (complexSpatialProjection c x)) k) ≤ M := by
  obtain ⟨C, hC, hCbound⟩ := exists_physical_bounded_extensions d
  obtain ⟨S, hS0, hS⟩ := exists_transitionSlope_bound
  let M := ((m + 1 : ℝ) * (2 * C) + S) * boxVolume (physicalBoxLower c) (physicalBoxUpper c)
  have hvol : 0 ≤ boxVolume (physicalBoxLower c) (physicalBoxUpper c) :=
    integral_nonneg (fun _ => by norm_num)
  refine ⟨M, mul_nonneg (by positivity) hvol, ?_⟩
  intro a τ ha ht ht' k
  obtain ⟨R, V, hR, hV, heq, hneg, hnonpos, hgeom⟩ := hCbound a τ ha ht ht'
  have hw (q : Option (Fin d) → ℂ) :
      normalCutoffWeight (OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q) k =
        normalCutoffWeight (R q) k := by
    by_cases hq : OAI.Analysis.Calculus.Current.physicalFiberDefining (1 / 10) a τ q < 0
    · rw [((heq q (le_of_lt hq)).1).eq_of_nhds]
    · rw [normalCutoffWeight_zero (le_of_not_gt hq), normalCutoffWeight_zero
        (le_of_not_gt (fun h => hq ((hneg q).mp h)))]
  calc
    _ = ∫ x in Icc (physicalBoxLower c) (physicalBoxUpper c),
        normalCutoffWeight (R (complexSpatialProjection c x)) k :=
      setIntegral_congr_fun measurableSet_Icc (fun x _ => hw _)
    _ ≤ M := physical_extension_cutoff_bound c hR hV hC.le hS hgeom k

end OAI.Analysis.PDE.Green
