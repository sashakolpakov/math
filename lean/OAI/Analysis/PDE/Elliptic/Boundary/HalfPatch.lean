import OAI.Analysis.PDE.Elliptic.Boundary.ConvexExtension
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.Perturbation

/-! Closed half-chart geometry and extension of the actual interior equation.
No equation on the flat boundary is assumed. -/

noncomputable section
open Set Metric InnerProductSpace
namespace OAI.Analysis.PDE.Elliptic

open OAI.Analysis.Normed.Function.Holder OAI.Analysis.PDE.Schauder

variable {m : ℕ}

def closedCoordinateHalfPatch (k : Fin m) (x₀ : EuclideanSpace ℝ (Fin m)) (ρ : ℝ) :
    Set (EuclideanSpace ℝ (Fin m)) := closedBall x₀ ρ ∩ {x | 0 ≤ x k}

theorem isCompact_closedCoordinateHalfPatch (k : Fin m) (x₀ : EuclideanSpace ℝ (Fin m))
    (ρ : ℝ) : IsCompact (closedCoordinateHalfPatch k x₀ ρ) :=
  (isCompact_closedBall x₀ ρ).inter_right (isClosed_le continuous_const (by fun_prop))

theorem convex_closedCoordinateHalfPatch (k : Fin m) (x₀ : EuclideanSpace ℝ (Fin m))
    (ρ : ℝ) : Convex ℝ (closedCoordinateHalfPatch k x₀ ρ) := by
  apply (convex_closedBall x₀ ρ).inter
  intro x hx y hy a b ha hb hab
  change 0 ≤ a * x k + b * y k
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

theorem nonempty_closedCoordinateHalfPatch (k : Fin m) (x₀ : EuclideanSpace ℝ (Fin m))
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hx₀ : x₀ k = 0) :
    (closedCoordinateHalfPatch k x₀ ρ).Nonempty :=
  ⟨x₀, mem_closedBall_self hρ, by simp only [Set.mem_ofPred_eq, hx₀, le_refl]⟩

theorem mem_closure_positive_coordinate_patch (k : Fin m)
    {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ U) (hxk : 0 ≤ x k) :
    x ∈ closure (U ∩ {y | 0 < y k}) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU x hx
  let t := min ε δ / 2
  have ht : 0 < t := half_pos (lt_min hε hδ)
  have htε : t < ε := by dsimp only [t]; linarith [min_le_left ε δ]
  have htδ : t < δ := by dsimp only [t]; linarith [min_le_right ε δ]
  let y := x + t • EuclideanSpace.single k (1 : ℝ)
  have hdist : dist y x = t := by
    simp [y, dist_eq_norm, norm_smul, abs_of_pos ht]
  refine ⟨y, ⟨hδU (by simpa only [mem_ball, hdist] using htδ), ?_⟩, ?_⟩
  · change 0 < x k + t * (EuclideanSpace.single k (1 : ℝ)) k
    simpa using add_pos_of_nonneg_of_pos hxk ht
  · simpa only [dist_comm x y, hdist] using htε

theorem equation_on_nonnegative_coordinate_patch
    {F : Type*} [TopologicalSpace F] [T2Space F]
    (k : Fin m) {U : Set (EuclideanSpace ℝ (Fin m))} (hU : IsOpen U)
    {f g : EuclideanSpace ℝ (Fin m) → F} (hf : Continuous f) (hg : Continuous g)
    (he : ∀ x ∈ U, 0 < x k → f x = g x) :
    ∀ x ∈ U, 0 ≤ x k → f x = g x := by
  intro x hx hxk
  exact (show EqOn f g (U ∩ {y | 0 < y k}) from fun y hy => he y hy.1 hy.2).closure
    hf hg (mem_closure_positive_coordinate_patch k hU hx hxk)

theorem continuous_nondivergenceOperator
    {A : EuclideanSpace ℝ (Fin m) → Matrix (Fin m) (Fin m) ℝ}
    (hA : Continuous A) {u : EuclideanSpace ℝ (Fin m) → ℝ}
    (hu : ContDiff ℝ 2 u) : Continuous (OAI.Analysis.PDE.Schauder.nondivergenceOperator A u) := by
  have hD₁ : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hD : Continuous (fderiv ℝ (fderiv ℝ u)) := hD₁.continuous_fderiv (by norm_num)
  unfold OAI.Analysis.PDE.Schauder.nondivergenceOperator
  fun_prop

end OAI.Analysis.PDE.Elliptic
