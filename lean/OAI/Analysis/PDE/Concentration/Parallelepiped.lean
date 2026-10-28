import OAI.Analysis.PDE.Concentration.Piola

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set _root_.MeasureTheory OAI.Analysis.PDE.Green

/-- Tangential divergence integrates to zero on a genuine parallelepiped
cell cut out by a regular sublevel. Face matching is expressed in the
contravariant components normal to the cell faces. -/
theorem integral_divergence_parallelepiped_sublevel_zero {m : ℕ}
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (F : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ)) (hF : ContDiff ℝ 1 F)
    {r : (Fin (m + 1) → ℝ) → ℝ} (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ L '' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hzero : ∀ x, r x = 0 → fderiv ℝ r x (F x) = 0)
    (hface : ∀ i, ∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      (r (L (i.insertNth (b i) y)) = r (L (i.insertNth (a i) y)) ∧
        linearPiola L F (i.insertNth (b i) y) i =
          linearPiola L F (i.insertNth (a i) y) i) ∨
      (0 ≤ r (L (i.insertNth (b i) y)) ∧ 0 ≤ r (L (i.insertNth (a i) y))) ∨
      (linearPiola L F (i.insertNth (b i) y) i = 0 ∧
        linearPiola L F (i.insertNth (a i) y) i = 0)) :
    (∫ x in L '' Icc a b ∩ {x | r x < 0}, coordinateDivergence F x) = 0 := by
  let G := linearPiola L F
  have hG : ContDiff ℝ 1 G := contDiff_linearPiola L hF
  have hrL : ContDiff ℝ 2 (r ∘ L) := hr.comp L.contDiff
  have hbase := OAI.Analysis.PDE.Green.integral_divergence_cell_sublevel_zero a b hab (fun i x => G x i)
    (fun i => (ContinuousLinearMap.proj i : (Fin (m + 1) → ℝ) →L[ℝ] ℝ).contDiff.comp hG)
    hrL (by
      intro x hx hz
      exact fderiv_comp_equiv_ne_zero L (hr.differentiable (by norm_num) _)
        (hrne _ (mem_image_of_mem L hx) hz))
    (by
      intro x hx
      rw [sum_fderiv_coordinate_mul, fderiv_linearPiola_normal L F
        (hr.differentiable (by norm_num) _)]
      exact hzero _ hx) hface
  have hbzero : (∫ x in Icc a b ∩ {x | r (L x) < 0}, coordinateDivergence F (L x)) = 0 := by
    convert hbase using 1
    apply setIntegral_congr_fun
      (measurableSet_Icc.inter ((isOpen_lt (hr.continuous.comp L.continuous) continuous_const).measurableSet))
    intro x hx
    dsimp only
    rw [← coordinateDivergence_linearPiola L (hF.differentiable (by norm_num) _)]
    exact coordinateDivergence_eq_components (hG.differentiable (by norm_num) _)
  have hset : L '' (Icc a b ∩ {x | r (L x) < 0}) = L '' Icc a b ∩ {x | r x < 0} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hrx⟩, rfl⟩
      exact ⟨mem_image_of_mem L hx, hrx⟩
    · rintro ⟨⟨x, hx, rfl⟩, hrx⟩
      exact ⟨x, ⟨hx, hrx⟩, rfl⟩
  have hJ := integral_image_eq_integral_abs_det_fderiv_smul volume
    (f := fun x => L x) (f' := fun _ => L.toContinuousLinearMap)
    (s := Icc a b ∩ {x | r (L x) < 0})
    (measurableSet_Icc.inter ((isOpen_lt (hr.continuous.comp L.continuous) continuous_const).measurableSet))
    (fun x hx => L.toContinuousLinearMap.hasFDerivAt.hasFDerivWithinAt)
    L.injective.injOn (coordinateDivergence F)
  rw [← hset, hJ]
  simp only [smul_eq_mul]
  rw [integral_const_mul, hbzero, mul_zero]

end OAI.Analysis.PDE.Concentration
