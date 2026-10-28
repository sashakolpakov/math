import OAI.Analysis.PDE.Dirichlet.Translation

open Set Filter Metric
open scoped Topology ComplexOrder

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem translated_patch_interior {n : ℕ} (r : CoordinateSpace n 4 → ℝ)
    (a : CoordinateSpace n 4) {R : ℝ} {y : CoordinateSpace n 4}
    (hy : y ∈ interior (sublevelPatch (fun z ↦ r (a + z)) R)) :
    a + y ∈ interior {z | r z ≤ 0} := by
  have hsub : sublevelPatch (fun z ↦ r (a + z)) R ⊆
      (fun z ↦ a + z) ⁻¹' {z | r z ≤ 0} := fun _ h ↦ h.1
  exact (Homeomorph.addLeft a).isOpenMap.interior_preimage_subset_preimage_interior
    (interior_mono hsub hy)

/-- The radius-one mixed estimate at an arbitrary boundary center. -/
theorem boundary_mixed_hessian_centered {n : ℕ} (hn : 1 ≤ n)
    {A : CoordinateSpace n 4 → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    {u r : CoordinateSpace n 4 → ℝ} {x e v : CoordinateSpace n 4}
    {B : CoordinateSpace n 4 →L[ℝ] CoordinateSpace n 4} {a C D F r₀ : ℝ}
    (hC : 0 ≤ C) (hD : 0 ≤ D) (hF : 0 ≤ F) (hr₀ : 0 < r₀)
    (hu : ContDiff ℝ 3 u) (hr : ContDiff ℝ 2 r) (hrx : r x = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x)
    (he : fderiv ℝ r x e = 0) (hBv : fderiv ℝ r x (B v) = 0)
    (hinward : fderiv ℝ r x v < 0)
    (hA : ∀ y ∈ interior {z | r z ≤ 0}, (OAI.LinearAlgebra.Moore.complexify (A y)).PosDef)
    (hconvex : ∀ y ∈ interior {z | r z ≤ 0},
      (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r y - r₀ •
        (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)))).PosSemidef)
    (hL : ∀ y ∈ interior {z | r z ≤ 0}, ‖y - x‖ ≤ 1 →
      |mooreLinearization A (affineDerivative u (e - B x) B) y| ≤ F * OAI.LinearAlgebra.Moore.mooreDifferential n (A y) 1)
    (hlevel : ∀ y, r y ≤ 0 → ‖y - x‖ ≤ 1 → r y = 0 →
      |affineDerivative u (e - B x) B y| ≤ C * ‖y - x‖ ^ 2)
    (hsize : ∀ y, r y ≤ 0 → ‖y - x‖ ≤ 1 → |affineDerivative u (e - B x) B y| ≤ D) :
    |fderiv ℝ (fderiv ℝ u) x v e| ≤ -((F + 8 * (C + D)) / r₀) * fderiv ℝ r x v := by
  let ut := fun y ↦ u (x + y)
  let rt := fun y ↦ r (x + y)
  let At := fun y ↦ A (x + y)
  have hut : ContDiff ℝ 3 ut := hu.comp (contDiff_const.add contDiff_id)
  have hrt : ContDiff ℝ 2 rt := hr.comp (contDiff_const.add contDiff_id)
  have hrt0 : rt 0 = 0 := by simpa [rt] using hrx
  have hfac : fderiv ℝ ut 0 = a • fderiv ℝ rt 0 := by
    simpa only [ut, rt, fderiv_comp_add_left, add_zero] using hfactor
  have het : fderiv ℝ rt 0 e = 0 := by simpa only [rt, fderiv_comp_add_left, add_zero] using he
  have hBvt : fderiv ℝ rt 0 (B v) = 0 := by simpa only [rt, fderiv_comp_add_left, add_zero] using hBv
  have hint : fderiv ℝ rt 0 v < 0 := by simpa only [rt, fderiv_comp_add_left, add_zero] using hinward
  have hXt : affineDerivative ut e B = fun y ↦ affineDerivative u (e - B x) B (x + y) := by
    funext y
    exact affineDerivative_translation u x e y B
  have h := boundary_mixed_hessian_on_patch hn (A := At) (R := 1) (by norm_num) hC hD hF hr₀
    hut hrt hrt0 hfac het hBvt hint
    (fun y hy ↦ hA (x + y) (translated_patch_interior r x hy))
    (fun y hy ↦ ?_) (fun y hy ↦ ?_) (fun y hy hry ↦ ?_) (fun y hy ↦ ?_)
  · simpa only [ut, rt, second_fderiv_translation, fderiv_comp_add_left, add_zero, one_pow, div_one] using h
  · simpa only [rt, quaternionHessian_translation] using
      hconvex (x + y) (translated_patch_interior r x hy)
  · rw [hXt, mooreLinearization_translation]
    have hy' : ‖(x + y) - x‖ ≤ 1 := by
      simpa only [add_sub_cancel_left, mem_closedBall, dist_zero_right] using (interior_subset hy).2
    exact hL (x + y) (translated_patch_interior r x hy) hy'
  · rw [hXt]
    have hy' : ‖(x + y) - x‖ ≤ 1 := by simpa [add_sub_cancel_left] using hy.2
    simpa only [add_sub_cancel_left] using hlevel (x + y) hy.1 hy' hry
  · rw [hXt]
    have hy' : ‖(x + y) - x‖ ≤ 1 := by simpa [add_sub_cancel_left] using hy.2
    exact hsize (x + y) hy.1 hy'

end OAI.Analysis.PDE.Dirichlet
