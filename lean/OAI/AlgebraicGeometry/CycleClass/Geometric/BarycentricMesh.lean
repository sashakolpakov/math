import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Module.Convex

/-! # Barycentric Mesh -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh

noncomputable section

/-!
# Quantitative mesh estimates for barycenters of nested faces

The points are actual vectors in a real normed space and their barycenters are
mathlib's `Finset.centroid`. No simplex mesh estimate is assumed.
-/

open scoped BigOperators

variable {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The centroid of a nonempty finite set is the arithmetic mean of its vertices. -/
theorem centroid_eq_inv_card_sum (s : Finset ι) (hs : s.Nonempty) (v : ι → E) :
    s.centroid ℝ v = (s.card : ℝ)⁻¹ • ∑ i ∈ s, v i := by
  rw [s.centroid_eq_centerMass hs,
    s.centerMass_eq_of_sum_1 v (s.sum_centroidWeights_eq_one_of_nonempty ℝ hs)]
  simp only [Finset.centroidWeights_apply, Finset.smul_sum]

/-- Subtracting a point commutes with taking the arithmetic mean. -/
theorem centroid_sub_eq_inv_card_sum (s : Finset ι) (hs : s.Nonempty)
    (v : ι → E) (x : E) :
    s.centroid ℝ v - x = (s.card : ℝ)⁻¹ • ∑ i ∈ s, (v i - x) := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
  rw [centroid_eq_inv_card_sum s hs v, Finset.sum_sub_distrib, smul_sub,
    Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

/-- The sum of vertex displacements from their centroid is zero. -/
theorem sum_sub_centroid_eq_zero (s : Finset ι) (hs : s.Nonempty) (v : ι → E) :
    ∑ i ∈ s, (v i - s.centroid ℝ v) = 0 := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
  rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    centroid_eq_inv_card_sum s hs v, smul_smul, mul_inv_cancel₀ hcard,
    one_smul, sub_self]

/-- A centroid remains within every closed ball containing all its vertices. -/
theorem dist_centroid_point_le (s : Finset ι) (hs : s.Nonempty) (v : ι → E)
    (x : E) (D : ℝ) (hD : ∀ i ∈ s, dist (v i) x ≤ D) :
    dist (s.centroid ℝ v) x ≤ D := by
  have hcard : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hs.card_pos)
  have hnonneg : 0 ≤ (s.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    dist (s.centroid ℝ v) x =
        ‖(s.card : ℝ)⁻¹ • ∑ i ∈ s, (v i - x)‖ := by
      rw [dist_eq_norm, centroid_sub_eq_inv_card_sum s hs v x]
    _ = (s.card : ℝ)⁻¹ * ‖∑ i ∈ s, (v i - x)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hnonneg]
    _ ≤ (s.card : ℝ)⁻¹ * ∑ i ∈ s, ‖v i - x‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le s _) hnonneg
    _ ≤ (s.card : ℝ)⁻¹ * ∑ _i ∈ s, D := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      exact Finset.sum_le_sum (fun i hi => by simpa only [dist_eq_norm] using hD i hi)
    _ = D := by
      rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

/-- Nested faces have barycenters closer by the exact missing-vertex proportion. -/
theorem dist_centroid_le_card_sdiff_div [DecidableEq ι]
    (v : ι → E) (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (D : ℝ) (hD : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤
      ((B \ A).card : ℝ) / (B.card : ℝ) * D := by
  have hB : B.Nonempty := hA.mono hAB
  have hnonneg : 0 ≤ (B.card : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hsum : (∑ i ∈ B, (v i - A.centroid ℝ v)) =
      ∑ i ∈ B \ A, (v i - A.centroid ℝ v) := by
    rw [← Finset.sum_sdiff hAB, sum_sub_centroid_eq_zero A hA v, add_zero]
  have hpoint (j : ι) (hj : j ∈ B) : ‖v j - A.centroid ℝ v‖ ≤ D := by
    rw [← dist_eq_norm, dist_comm]
    exact dist_centroid_point_le A hA v (v j) D (fun i hi => hD i (hAB hi) j hj)
  calc
    dist (A.centroid ℝ v) (B.centroid ℝ v) =
        ‖(B.card : ℝ)⁻¹ • ∑ i ∈ B \ A, (v i - A.centroid ℝ v)‖ := by
      rw [dist_comm, dist_eq_norm, centroid_sub_eq_inv_card_sum B hB v, hsum]
    _ = (B.card : ℝ)⁻¹ * ‖∑ i ∈ B \ A, (v i - A.centroid ℝ v)‖ := by
      rw [norm_smul, Real.norm_of_nonneg hnonneg]
    _ ≤ (B.card : ℝ)⁻¹ * ∑ i ∈ B \ A, ‖v i - A.centroid ℝ v‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le (B \ A) _) hnonneg
    _ ≤ (B.card : ℝ)⁻¹ * ∑ _i ∈ B \ A, D := by
      apply mul_le_mul_of_nonneg_left _ hnonneg
      exact Finset.sum_le_sum (fun i hi => hpoint i (Finset.mem_sdiff.mp hi).1)
    _ = ((B \ A).card : ℝ) / (B.card : ℝ) * D := by
      rw [Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
      ring

/-- The exact estimate expressed as the difference of the two face cardinalities. -/
theorem dist_centroid_le_card_sub_div [DecidableEq ι]
    (v : ι → E) (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (D : ℝ) (hD : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤
      ((B.card : ℝ) - (A.card : ℝ)) / (B.card : ℝ) * D := by
  simpa only [Finset.card_sdiff_of_subset hAB, Nat.cast_sub (Finset.card_le_card hAB)]
    using dist_centroid_le_card_sdiff_div v A B hA hAB D hD

/-- A nonempty nested pair of faces with at most `n+1` vertices contracts by `n/(n+1)`. -/
theorem dist_centroid_le_dimension_factor_of_subset [DecidableEq ι]
    (v : ι → E) (A B : Finset ι) (hA : A.Nonempty) (hAB : A ⊆ B)
    (n : ℕ) (hcard : B.card ≤ n + 1)
    (D : ℝ) (hD : ∀ i ∈ B, ∀ j ∈ B, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤ (n : ℝ) / (n + 1) * D := by
  have hD0 : 0 ≤ D := by
    obtain ⟨i, hi⟩ := hA
    simpa only [dist_self] using hD i (hAB hi) i (hAB hi)
  have ha1 : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hA.card_pos
  have hbpos : (0 : ℝ) < (B.card : ℝ) := by
    exact_mod_cast (hA.mono hAB).card_pos
  have hbn : (B.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hproduct : (B.card : ℝ) ≤ (A.card : ℝ) * ((n : ℝ) + 1) := by
    have hmul := mul_le_mul_of_nonneg_right ha1 (le_of_lt hn)
    nlinarith
  have hratio : ((B.card : ℝ) - (A.card : ℝ)) / (B.card : ℝ) ≤
      (n : ℝ) / (n + 1) := by
    apply (div_le_div_iff₀ hbpos hn).2
    nlinarith
  exact (dist_centroid_le_card_sub_div v A B hA hAB D hD).trans
    (mul_le_mul_of_nonneg_right hratio hD0)

/-- Any two comparable nonempty faces of `n+1` actual vertices satisfy the mesh bound. -/
theorem dist_centroid_le_dimension_factor {n : ℕ}
    (v : Fin (n + 1) → E) (A B : Finset (Fin (n + 1)))
    (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A ⊆ B ∨ B ⊆ A)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    dist (A.centroid ℝ v) (B.centroid ℝ v) ≤ (n : ℝ) / (n + 1) * D := by
  have hcard (C : Finset (Fin (n + 1))) : C.card ≤ n + 1 := by
    simpa only [Fintype.card_fin] using C.card_le_univ
  rcases hAB with hAB | hBA
  · exact dist_centroid_le_dimension_factor_of_subset v A B hA hAB n (hcard B) D
      (fun i _ j _ => hD i j)
  · rw [dist_comm]
    exact dist_centroid_le_dimension_factor_of_subset v B A hB hBA n (hcard A) D
      (fun i _ j _ => hD i j)

/-- The same mesh bound holds throughout the convex hull of a chain of face barycenters. -/
theorem dist_convexHull_centroids_le_dimension_factor {κ : Type*} {n : ℕ}
    (v : Fin (n + 1) → E) (faces : κ → Finset (Fin (n + 1)))
    (hne : ∀ k, (faces k).Nonempty)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D)
    {x y : E}
    (hx : x ∈ convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v))
    (hy : y ∈ convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v)) :
    dist x y ≤ (n : ℝ) / (n + 1) * D := by
  obtain ⟨x', ⟨k, rfl⟩, y', ⟨l, rfl⟩, hxy⟩ := convexHull_exists_dist_ge2 hx hy
  exact hxy.trans
    (dist_centroid_le_dimension_factor v (faces k) (faces l) (hne k) (hne l)
      (hchain k l) D hD)

/-- Barycentric subdivision of a finite simplex has mesh at most `n/(n+1)` times its vertex bound. -/
theorem diam_convexHull_centroids_le_dimension_factor {κ : Type*} {n : ℕ}
    (v : Fin (n + 1) → E) (faces : κ → Finset (Fin (n + 1)))
    (hne : ∀ k, (faces k).Nonempty)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k)
    (D : ℝ) (hD : ∀ i j, dist (v i) (v j) ≤ D) :
    Metric.diam (convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v)) ≤
      (n : ℝ) / (n + 1) * D := by
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hD 0 0
  apply Metric.diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  exact dist_convexHull_centroids_le_dimension_factor v faces hne hchain D hD hx hy

/-- The geometric mesh estimate with the actual diameter of the original simplex. -/
theorem diam_face_chain_le_simplex_diam {κ : Type*} {n : ℕ}
    (v : Fin (n + 1) → E) (faces : κ → Finset (Fin (n + 1)))
    (hne : ∀ k, (faces k).Nonempty)
    (hchain : ∀ k l, faces k ⊆ faces l ∨ faces l ⊆ faces k) :
    Metric.diam (convexHull ℝ (Set.range fun k => (faces k).centroid ℝ v)) ≤
      (n : ℝ) / (n + 1) * Metric.diam (convexHull ℝ (Set.range v)) := by
  have hD (i j : Fin (n + 1)) : dist (v i) (v j) ≤ Metric.diam (Set.range v) :=
    Metric.dist_le_diam_of_mem (Set.finite_range v).isBounded
      (Set.mem_range_self i) (Set.mem_range_self j)
  simpa only [convexHull_diam] using
    diam_convexHull_centroids_le_dimension_factor v faces hne hchain
      (Metric.diam (Set.range v)) hD

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.BarycentricMesh
