import OAI.Analysis.PDE.Schauder.Calculus.Boundary.SchauderZero
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Stability

/-! Reduction of the full flat-boundary estimate to an actual boundary jet lifting. -/

noncomputable section
open Set Metric InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem laplacian_holder_of_hessian_holder {m : ℕ}
    (u : EuclideanSpace ℝ (Fin m) → ℝ) {α H : ℝ}
    (x y : EuclideanSpace ℝ (Fin m))
    (hh : ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤ H * ‖x - y‖ ^ α) :
    |laplacian u x - laplacian u y| ≤ (m : ℝ) * H * ‖x - y‖ ^ α := by
  simp only [laplacian_coordinate, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i : Fin m, |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) -
        fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin m, H * ‖x - y‖ ^ α := by
      apply Finset.sum_le_sum
      intro i _
      exact (euclidean_bilinear_entry_le_norm
        (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y) i i).trans hh
    _ = _ := by simp; ring

theorem halfspace_schauder_from_lift {m : ℕ} (hm : 3 ≤ m) (k : Fin m)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C > 0, ∀ (u W : EuclideanSpace ℝ (Fin m) → ℝ),
      ContDiff ℝ 2 u → ContDiff ℝ 2 W → HasCompactSupport u → HasCompactSupport W →
      (∀ x, x k = 0 → u x = 0) → (∀ x, x k = 0 → W x = 0) →
      (∀ x, x k = 0 → laplacian W x = laplacian u x) →
      ∀ H L, 0 ≤ H → 0 ≤ L →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        |laplacian u x - laplacian u y| ≤ H * ‖x - y‖ ^ α) →
      (∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y‖ ≤ L * ‖x - y‖ ^ α) →
      ∀ x, 0 ≤ x k → ∀ y, 0 ≤ y k →
        ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y‖ ≤
          (C * (H + m * L) + L) * ‖x - y‖ ^ α := by
  obtain ⟨C, hC, hb⟩ := halfspace_schauder_zero_trace_forcing hm k hα hα1
  refine ⟨C, hC, ?_⟩
  intro u W hu hW huc hWc hzero hWzero hmatch H L hH hL hHolder hWHolder x hx y hy
  let v := fun z => u z - W z
  have hv : ContDiff ℝ 2 v := hu.sub hW
  have hvc : HasCompactSupport v := huc.sub hWc
  have hlap (z) : laplacian v z = laplacian u z - laplacian W z :=
    hu.contDiffAt.laplacian_sub hW.contDiffAt
  have hz (z) (hz' : z k = 0) : v z = 0 := by simp [v, hzero z hz', hWzero z hz']
  have hlz (z) (hz' : z k = 0) : laplacian v z = 0 := by rw [hlap, hmatch z hz', sub_self]
  have hforce (a) (ha : 0 ≤ a k) (b) (hb' : 0 ≤ b k) :
      |laplacian v a - laplacian v b| ≤ (H + m * L) * ‖a - b‖ ^ α := by
    rw [hlap, hlap]
    calc
      _ = |(laplacian u a - laplacian u b) - (laplacian W a - laplacian W b)| := by congr 1; ring
      _ ≤ |laplacian u a - laplacian u b| + |laplacian W a - laplacian W b| := abs_sub _ _
      _ ≤ H * ‖a - b‖ ^ α + (m : ℝ) * L * ‖a - b‖ ^ α :=
        add_le_add (hHolder a ha b hb') (laplacian_holder_of_hessian_holder W a b (hWHolder a ha b hb'))
      _ = _ := by ring
  have hvHolder := hb v hv hvc hz hlz (H + m * L) (by positivity) hforce x hx y hy
  have heq : fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) y =
      (fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y) +
      (fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y) := by
    rw [second_fderiv_sub u W hu hW, second_fderiv_sub u W hu hW]
    abel
  rw [heq]
  calc
    _ ≤ ‖fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y‖ +
        ‖fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y‖ := by
      simpa only using! norm_add_le
        (fderiv ℝ (fderiv ℝ v) x - fderiv ℝ (fderiv ℝ v) y)
        (fderiv ℝ (fderiv ℝ W) x - fderiv ℝ (fderiv ℝ W) y)
    _ ≤ C * (H + m * L) * ‖x - y‖ ^ α + L * ‖x - y‖ ^ α :=
      add_le_add hvHolder (hWHolder x hx y hy)
    _ = _ := by ring

end OAI.Analysis.PDE.Schauder
