import OAI.AlgebraicTopology.Cohomology.Singular.Smooth
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Simplex Form Domain -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexFormDomain.Constructions

noncomputable section

/-! A full-dimensional coordinate simplex for restricting differential forms. -/

open scoped OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

open Set
open scoped BigOperators ContDiff

def coordinateSimplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

theorem coordinateSimplex_zero (n : ℕ) : (0 : Fin n → ℝ) ∈ coordinateSimplex n := by
  constructor
  · intro i; exact le_rfl
  · simp

theorem coordinateSimplex_convex (n : ℕ) : Convex ℝ (coordinateSimplex n) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · change ∑ i, (a * x i + b * y i) ≤ 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      a * ∑ i, x i + b * ∑ i, y i ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hx.2 ha) (mul_le_mul_of_nonneg_left hy.2 hb)
      _ = 1 := by simpa only [mul_one] using hab

theorem coordinateSimplex_starConvex (n : ℕ) :
    StarConvex ℝ (0 : Fin n → ℝ) (coordinateSimplex n) :=
  (coordinateSimplex_convex n).starConvex (coordinateSimplex_zero n)

theorem coordinateSimplex_interior_nonempty (n : ℕ) :
    (interior (coordinateSimplex n)).Nonempty := by
  let U : Set (Fin n → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1}
  have hU : IsOpen U := by
    have hcoord : IsOpen {x : Fin n → ℝ | ∀ i, 0 < x i} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    exact hcoord.inter (isOpen_lt (continuous_finsetSum _ fun i _ => continuous_apply i)
      continuous_const)
  have hsub : U ⊆ coordinateSimplex n := fun _ hx =>
    ⟨fun i => (hx.1 i).le, hx.2.le⟩
  let x : Fin n → ℝ := fun _ => 1 / ((n : ℝ) + 1)
  have hx : x ∈ U := by
    constructor
    · intro i
      exact one_div_pos.mpr (by positivity)
    · change ∑ _i : Fin n, 1 / ((n : ℝ) + 1) < 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [mul_one_div, div_lt_iff₀ (by positivity)]
      linarith
  exact ⟨x, hU.subset_interior_iff.mpr hsub hx⟩

theorem coordinateSimplex_uniqueDiffOn (n : ℕ) : UniqueDiffOn ℝ (coordinateSimplex n) :=
  uniqueDiffOn_convex (coordinateSimplex_convex n) (coordinateSimplex_interior_nonempty n)

theorem coordinateSimplex_isClosed (n : ℕ) : IsClosed (coordinateSimplex n) := by
  have hcoord : IsClosed {x : Fin n → ℝ | ∀ i, 0 ≤ x i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact hcoord.inter (isClosed_le (continuous_finsetSum _ fun i _ => continuous_apply i)
    continuous_const)

theorem coordinateSimplex_isCompact (n : ℕ) : IsCompact (coordinateSimplex n) := by
  apply (isCompact_Icc (a := (0 : Fin n → ℝ)) (b := 1)).of_isClosed_subset
    (coordinateSimplex_isClosed n)
  intro x hx
  refine ⟨hx.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)).trans hx.2

/-- Add the last barycentric coordinate to an ordinary coordinate vector. -/
def simplexBarycentric (n : ℕ) (x : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.snoc x (1 - ∑ i, x i)

@[simp] theorem simplexBarycentric_castSucc (n : ℕ) (x : Fin n → ℝ) (i : Fin n) :
    simplexBarycentric n x i.castSucc = x i := Fin.snoc_castSucc _ _ _

@[simp] theorem simplexBarycentric_last (n : ℕ) (x : Fin n → ℝ) :
    simplexBarycentric n x (Fin.last n) = 1 - ∑ i, x i := Fin.snoc_last _ _

theorem simplexBarycentric_sum (n : ℕ) (x : Fin n → ℝ) :
    ∑ i, simplexBarycentric n x i = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp only [simplexBarycentric_castSucc, simplexBarycentric_last]
  ring

theorem simplexBarycentric_nonneg {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ coordinateSimplex n) (i : Fin (n + 1)) : 0 ≤ simplexBarycentric n x i := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [simplexBarycentric_last]
    exact sub_nonneg.mpr hx.2
  · rw [simplexBarycentric_castSucc]
    exact hx.1 j

/-- The barycentric coordinates as a point of the standard simplex. -/
def simplexBarycentricPoint {n : ℕ} (x : Fin n → ℝ) (hx : x ∈ coordinateSimplex n) :
    Convexity.StdSimplex ℝ (Fin (n + 1)) :=
  Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (simplexBarycentric n x)
    (simplexBarycentric_nonneg hx) (simplexBarycentric_sum n x)

@[simp]
theorem simplexBarycentricPoint_weights {n : ℕ} (x : Fin n → ℝ)
    (hx : x ∈ coordinateSimplex n) :
    ((simplexBarycentricPoint x hx).weights : Fin (n + 1) → ℝ) = simplexBarycentric n x := by
  funext i
  exact Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates_weights _ _ _ _

theorem simplexBarycentric_mem {n : ℕ} {x : Fin n → ℝ} (hx : x ∈ coordinateSimplex n) :
    simplexBarycentric n x ∈ Set.range (fun y : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (y.weights : Fin (n + 1) → ℝ)) :=
  ⟨simplexBarycentricPoint x hx, simplexBarycentricPoint_weights x hx⟩

theorem simplexBarycentric_contDiff (n : ℕ) : ContDiff ℝ ∞ (simplexBarycentric n) := by
  apply contDiff_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [simplexBarycentric_last]
    exact contDiff_const.sub (ContDiff.sum fun j _ => contDiff_apply ℝ ℝ j)
  · simpa only [simplexBarycentric_castSucc] using (contDiff_apply ℝ ℝ j)

end

end OAI.AlgebraicTopology.Kunneth.SimplexFormDomain.Constructions
