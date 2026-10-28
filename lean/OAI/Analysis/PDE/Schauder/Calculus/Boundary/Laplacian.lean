import OAI.Analysis.PDE.Schauder.Calculus.Boundary.C2Reflection

/-! The actual reflected Poisson equation at a flat zero-Dirichlet boundary. -/

noncomputable section
open Set InnerProductSpace Laplacian
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

theorem normalReflection_coordinate {m : ℕ} (k j : Fin m) :
    normalReflection (EuclideanSpace.single k (1 : ℝ)) (EuclideanSpace.single j (1 : ℝ)) =
      if j = k then -EuclideanSpace.single j 1 else EuclideanSpace.single j 1 := by
  rw [normalReflection_apply _ _ (by simp)]
  by_cases hj : j = k
  · subst j
    simp only []
    simp [two_smul]
  · simp [hj, Ne.symm hj, EuclideanSpace.inner_single_left]

theorem laplacian_eq_normal_boundary {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (hzero : ∀ x, x k = 0 → u x = 0) (x : EuclideanSpace ℝ (Fin m)) (hx : x k = 0) :
    laplacian u x = fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
  rw [laplacian_coordinate]
  apply Finset.sum_eq_single k
  · intro j _ hj
    apply flat_boundary_hessian_zero u hu (EuclideanSpace.single k 1) x _ _ (by simp)
    · simpa [EuclideanSpace.inner_single_left] using hx
    · simp [EuclideanSpace.inner_single_left, Ne.symm hj]
    · simp [EuclideanSpace.inner_single_left, Ne.symm hj]
    · intro y hy
      exact hzero y (by simpa [EuclideanSpace.inner_single_left] using hy)
  · simp

theorem contDiff_odd_of_boundary_laplacian_zero {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (hzero : ∀ x, x k = 0 → u x = 0)
    (hlap : ∀ x, x k = 0 → laplacian u x = 0) :
    ContDiff ℝ 2 (oddNormalExtension (EuclideanSpace.single k 1) u) := by
  apply contDiff_oddNormalExtension _ (by simp) u hu
  · intro x hx
    exact hzero x (by simpa [EuclideanSpace.inner_single_left] using hx)
  · intro x hx
    have hx' : x k = 0 := by simpa [EuclideanSpace.inner_single_left] using hx
    rw [← laplacian_eq_normal_boundary k u hu hzero x hx']
    exact hlap x hx'

theorem laplacian_oddNormalExtension {m : ℕ} (k : Fin m)
    (u : EuclideanSpace ℝ (Fin m) → ℝ) (hu : ContDiff ℝ 2 u)
    (hzero : ∀ x, x k = 0 → u x = 0)
    (hlap : ∀ x, x k = 0 → laplacian u x = 0) (x : EuclideanSpace ℝ (Fin m)) :
    laplacian (oddNormalExtension (EuclideanSpace.single k 1) u) x =
      oddNormalExtension (EuclideanSpace.single k 1) (laplacian u) x := by
  let e := EuclideanSpace.single k (1 : ℝ)
  have he : ‖e‖ = 1 := by simp [e]
  have hz (x) (hx : inner ℝ e x = 0) : u x = 0 :=
    hzero x (by simpa [e, EuclideanSpace.inner_single_left] using hx)
  have hn (x) (hx : inner ℝ e x = 0) : fderiv ℝ (fderiv ℝ u) x e e = 0 := by
    have hx' : x k = 0 := by simpa [e, EuclideanSpace.inner_single_left] using hx
    rw [← laplacian_eq_normal_boundary k u hu hzero x hx']
    exact hlap x hx'
  rw [laplacian_coordinate]
  change (∑ j : Fin m, fderiv ℝ (fderiv ℝ (oddNormalExtension e u)) x
    (EuclideanSpace.single j 1) (EuclideanSpace.single j 1)) = oddNormalExtension e (laplacian u) x
  simp_rw [second_fderiv_oddNormalExtension e he u hu hz hn]
  by_cases hx : 0 ≤ inner ℝ e x
  · simp only [ite_eq_left hx, oddNormalExtension]
    rw [laplacian_coordinate]
  · simp only [ite_eq_right hx, oddNormalExtension]
    rw [laplacian_coordinate, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [e]
    rw [normalReflection_coordinate]
    by_cases hj : j = k <;> simp [hj]

end OAI.Analysis.PDE.Schauder
