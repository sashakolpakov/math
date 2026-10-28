import OAI.AlgebraicTopology.DeRham.Comparison.StokesF
import OAI.Geometry.Foundations.ConvexStdSimplexMetric
import Mathlib.Algebra.BigOperators.Fin

/-! # Duffy Coordinates -/

namespace OAI.AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy

/-!
# Polynomial Duffy coordinates from cubes to barycentric simplices

The recursive map has first coordinate `t₀` and remaining coordinates
`(1-t₀) Dₙ(tail t)`. It is defined on the entire ambient real vector space,
is smooth of every order, and sends the actual closed unit cube into the
standard barycentric simplex.
-/

open Set
open scoped BigOperators ContDiff OAI.Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex

/-- The genuine recursive Duffy polynomial in barycentric coordinates. -/
def coordinates : (n : ℕ) → (Fin n → ℝ) → (Fin (n + 1) → ℝ)
  | 0, _ => fun _ => 1
  | n + 1, t => Fin.cons (t 0) (fun j => (1 - t 0) * coordinates n (Fin.tail t) j)

@[simp]
theorem coordinates_zero (t : Fin 0 → ℝ) (j : Fin 1) : Duffy.coordinates 0 t j = 1 := rfl

theorem coordinates_succ (n : ℕ) (t : Fin (n + 1) → ℝ) :
    Duffy.coordinates (n + 1) t =
      Fin.cons (t 0) (fun j => (1 - t 0) * Duffy.coordinates n (Fin.tail t) j) := rfl

@[simp]
theorem coordinates_succ_zero (n : ℕ) (t : Fin (n + 1) → ℝ) :
    Duffy.coordinates (n + 1) t 0 = t 0 := rfl

@[simp]
theorem coordinates_succ_succ (n : ℕ) (t : Fin (n + 1) → ℝ) (j : Fin (n + 1)) :
    Duffy.coordinates (n + 1) t j.succ = (1 - t 0) * Duffy.coordinates n (Fin.tail t) j := rfl

@[simp]
theorem coordinates_succ_cons (n : ℕ) (a : ℝ) (t : Fin n → ℝ) :
    Duffy.coordinates (n + 1) (Fin.cons a t) =
      Fin.cons a (fun j => (1 - a) * Duffy.coordinates n t j) := by
  rw [coordinates_succ]
  simp only [Fin.cons_zero, Fin.tail_cons]

/-- Every coordinate is a polynomial expression, hence smooth at every order. -/
theorem contDiff_coordinates (n : ℕ) (r : ℕ∞ω) : ContDiff ℝ r (Duffy.coordinates n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
    apply contDiff_pi.mpr
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact contDiff_apply (𝕜 := ℝ) (E := ℝ) 0
    · change ContDiff ℝ r (fun t : Fin (n + 1) → ℝ =>
        (1 - t 0) * Duffy.coordinates n (Fin.tail t) k)
      have htail : ContDiff ℝ r (Fin.tail : (Fin (n + 1) → ℝ) → (Fin n → ℝ)) :=
        contDiff_pi.mpr fun i => contDiff_apply (𝕜 := ℝ) (E := ℝ) i.succ
      exact (contDiff_const.sub (contDiff_apply (𝕜 := ℝ) (E := ℝ) 0)).mul
        ((contDiff_pi.mp ih k).comp htail)

theorem continuous_coordinates (n : ℕ) : Continuous (Duffy.coordinates n) :=
  (contDiff_coordinates n ∞).continuous

/-- The barycentric coordinates sum to one even outside the cube. -/
theorem sum_coordinates (n : ℕ) : ∀ t : Fin n → ℝ, ∑ j, Duffy.coordinates n t j = 1 := by
  induction n with
  | zero => intro t; simp [Duffy.coordinates]
  | succ n ih =>
    intro t
    rw [Fin.sum_univ_succ]
    simp only [coordinates_succ_zero, coordinates_succ_succ]
    rw [← Finset.mul_sum, ih]
    ring

/-- On the unit cube all barycentric coordinates are nonnegative. -/
theorem coordinates_nonneg (n : ℕ) :
    ∀ (t : Fin n → ℝ), t ∈ StokesF.SingularCubeStokes.unitCube n →
      ∀ j, 0 ≤ Duffy.coordinates n t j := by
  induction n with
  | zero => intro t _ j; exact zero_le_one
  | succ n ih =>
    intro t ht j
    have htail : Fin.tail t ∈ StokesF.SingularCubeStokes.unitCube n :=
      ⟨fun i => ht.1 i.succ, fun i => ht.2 i.succ⟩
    refine Fin.cases ?_ (fun k => ?_) j
    · exact ht.1 0
    · exact mul_nonneg (sub_nonneg.mpr (ht.2 0)) (ih (Fin.tail t) htail k)

/-- The polynomial sends the actual cube into the actual standard simplex. -/
theorem coordinates_mem_stdSimplex {n : ℕ} {t : Fin n → ℝ}
    (ht : t ∈ StokesF.SingularCubeStokes.unitCube n) :
    Duffy.coordinates n t ∈ Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (x : Fin (n + 1) → ℝ)) := by
  refine ⟨Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (Duffy.coordinates n t)
    (coordinates_nonneg n t ht) (sum_coordinates n t), ?_⟩
  funext i
  simp [Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates]

theorem mapsTo_coordinates (n : ℕ) :
    MapsTo (Duffy.coordinates n) (StokesF.SingularCubeStokes.unitCube n) (Set.range (fun x : Convexity.StdSimplex ℝ (Fin (n + 1)) =>
      (x : Fin (n + 1) → ℝ))) :=
  fun _ ht => coordinates_mem_stdSimplex ht

/-- Duffy coordinates as a continuous map between the closed cube and simplex. -/
noncomputable def toSimplex (n : ℕ) :
    C(StokesF.SingularCubeStokes.unitCube n, Convexity.StdSimplex ℝ (Fin (n + 1))) where
  toFun t := Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates (Duffy.coordinates n t.val)
    (coordinates_nonneg n t.val t.property) (sum_coordinates n t.val)
  continuous_toFun := by
    apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (n + 1))).continuous_iff.mpr
    simpa [Function.comp_def, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates] using
      (continuous_coordinates n).comp continuous_subtype_val

@[simp]
theorem toSimplex_val (n : ℕ) (t : StokesF.SingularCubeStokes.unitCube n) :
    (toSimplex n t : Fin (n + 1) → ℝ) = Duffy.coordinates n t.val := by
  funext i
  simp [toSimplex, Geometry.Foundations.ConvexStdSimplexMetric.Convexity.StdSimplex.ofCoordinates]

/-- Each coordinate before the last is its cube coordinate times all earlier
remaining factors. This is the closed polynomial expression for the recursion. -/
theorem coordinates_castSucc_filter (n : ℕ) :
    ∀ (t : Fin n → ℝ) (j : Fin n),
      Duffy.coordinates n t j.castSucc =
        t j * ∏ k : Fin n with k < j, (1 - t k) := by
  induction n with
  | zero => intro _ j; exact Fin.elim0 j
  | succ n ih =>
    intro t j
    refine Fin.cases ?_ (fun k => ?_) j
    · simp
    · change (1 - t 0) * Duffy.coordinates n (Fin.tail t) k.castSucc =
        t k.succ * ∏ l : Fin (n + 1) with l < k.succ, (1 - t l)
      rw [ih]
      simp only [Finset.prod_filter, Fin.prod_univ_succ, Fin.succ_pos, ite_true,
        Fin.succ_lt_succ_iff, Fin.tail]
      ring

/-- The usual product notation over indices strictly smaller than `j`. -/
theorem coordinates_castSucc (n : ℕ) (t : Fin n → ℝ) (j : Fin n) :
    Duffy.coordinates n t j.castSucc = t j * ∏ k ∈ Finset.Iio j, (1 - t k) := by
  simpa only [Finset.filter_gt_eq_Iio] using coordinates_castSucc_filter n t j

/-- The last barycentric coordinate is the product of all remaining factors. -/
theorem coordinates_last (n : ℕ) :
    ∀ t : Fin n → ℝ, Duffy.coordinates n t (Fin.last n) = ∏ k : Fin n, (1 - t k) := by
  induction n with
  | zero => intro t; simp
  | succ n ih =>
    intro t
    change (1 - t 0) * Duffy.coordinates n (Fin.tail t) (Fin.last n) =
      ∏ k : Fin (n + 1), (1 - t k)
    rw [ih, Fin.prod_univ_succ]
    rfl

end OAI.AlgebraicTopology.DeRham.Comparison.DuffyCoordinates.Duffy
