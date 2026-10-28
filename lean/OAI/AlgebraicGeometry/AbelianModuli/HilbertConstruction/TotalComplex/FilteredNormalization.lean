import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.CycleNormalization

/-! # Filtered Normalization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.FilteredNormalization

noncomputable section

/-! Row normalization when the differential is concentrated in its final row. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

theorem zeroRowsBefore_mono {n k l : ℕ} {x : (K.total (.up ℕ)).X n}
    (h : CycleNormalization.ZeroRowsBefore K n x l) (hkl : k ≤ l) : CycleNormalization.ZeroRowsBefore K n x k := by
  intro a b hab ha
  exact h a b hab (lt_of_lt_of_le ha hkl)

/-- Subtracting a boundary leaves the differential unchanged. -/
theorem total_sub_boundary_d (n : ℕ) (x : (K.total (.up ℕ)).X (n + 1))
    (z : (K.total (.up ℕ)).X n) :
    (K.total (.up ℕ)).d (n + 1) (n + 2)
      (x - (K.total (.up ℕ)).d n (n + 1) z) =
        (K.total (.up ℕ)).d (n + 1) (n + 2) x := by
  rw [map_sub]
  have hz : (K.total (.up ℕ)).d (n + 1) (n + 2)
      ((K.total (.up ℕ)).d n (n + 1) z) = 0 := by
    change ((K.total (.up ℕ)).d n (n + 1) ≫
      (K.total (.up ℕ)).d (n + 1) (n + 2)) z = 0
    rw [(K.total (.up ℕ)).d_comp_d]
    rfl
  rw [hz, sub_zero]

/-- Only the relevant output coordinate must vanish to obtain the row-cycle condition. -/
theorem row_cycle_of_output_coordinate_zero (n q p : ℕ) (hdeg : q + p = n)
    (x : (K.total (.up ℕ)).X n) (hbefore : CycleNormalization.ZeroRowsBefore K n x q)
    (himage : FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K q (p + 1) (n + 1)
      ((K.total (.up ℕ)).d n (n + 1) x) = 0) :
    (K.X q).d p (p + 1) (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K q p n x) = 0 := by
  cases q with
  | zero =>
      have hn : p = n := by omega
      clear hdeg
      subst n
      have h := congrArg (fun f => f x) (BoundaryCoordinates.total_d_π_zero K p)
      exact h.symm.trans himage
  | succ q =>
      have hn : q + p + 1 = n := by omega
      clear hdeg
      subst n
      have h := congrArg (fun f => f x) (BoundaryCoordinates.total_d_π_interior K q p)
      have hc : (K.d q (q + 1)).f (p + 1)
          (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K q (p + 1) (q + p + 1) x) +
        ((-1 : ℤˣ) ^ (q + 1)) • (K.X (q + 1)).d p (p + 1)
          (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (q + 1) p (q + p + 1) x) = 0 := by
        simpa [ConcreteCategory.comp_apply, Units.smul_def] using h.symm.trans himage
      rw [hbefore q (p + 1) (by omega) (by omega), map_zero, zero_add] at hc
      exact (smul_eq_zero_iff_eq _).mp hc

/-- The next row can be removed if the differential has no output in that row. -/
theorem exists_remove_row_of_image_zero (q p : ℕ)
    (x : (K.total (.up ℕ)).X (q + p + 1))
    (hbefore : CycleNormalization.ZeroRowsBefore K (q + p + 1) x q)
    (himage : CycleNormalization.ZeroRowsBefore K (q + p + 2)
      ((K.total (.up ℕ)).d (q + p + 1) (q + p + 2) x) (q + 1))
    (hrows : CycleNormalization.RowsExact K) :
    ∃ z : (K.total (.up ℕ)).X (q + p),
      CycleNormalization.ZeroRowsBefore K (q + p + 1)
        (x - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) (q + 1) := by
  have hc := row_cycle_of_output_coordinate_zero K (q + p + 1) q (p + 1)
    (by omega) x hbefore (himage q (p + 2) (by omega) (by omega))
  obtain ⟨z, hz, hpreserve⟩ := RowElimination.exists_remove_row_coordinate K q p x (hrows q p) hc
  refine ⟨z, ?_⟩
  intro a b hab ha
  by_cases haq : a < q
  · rw [hpreserve a b haq]
    exact hbefore a b hab haq
  · have heqa : a = q := by omega
    have heqb : b = p + 1 := by omega
    subst a b
    exact hz

/-- Fixed-degree version of the row-removal step. -/
theorem exists_remove_row_of_image_zero_of_lt (n q : ℕ) (hq : q < n + 1)
    (x : (K.total (.up ℕ)).X (n + 1)) (hbefore : CycleNormalization.ZeroRowsBefore K (n + 1) x q)
    (himage : CycleNormalization.ZeroRowsBefore K (n + 2)
      ((K.total (.up ℕ)).d (n + 1) (n + 2) x) (q + 1)) (hrows : CycleNormalization.RowsExact K) :
    ∃ z : (K.total (.up ℕ)).X n,
      CycleNormalization.ZeroRowsBefore K (n + 1)
        (x - (K.total (.up ℕ)).d n (n + 1) z) (q + 1) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hq)
  exact exists_remove_row_of_image_zero K q p x hbefore himage hrows

/-- If the differential vanishes in the rows being eliminated, subtracting a boundary
normalizes the input to its final row without changing that differential. -/
theorem exists_normalize_from_image (n : ℕ) (x : (K.total (.up ℕ)).X (n + 1))
    (himage : CycleNormalization.ZeroRowsBefore K (n + 2)
      ((K.total (.up ℕ)).d (n + 1) (n + 2) x) (n + 1)) (hrows : CycleNormalization.RowsExact K) :
    ∃ z : (K.total (.up ℕ)).X n,
      CycleNormalization.ZeroRowsBefore K (n + 1)
        (x - (K.total (.up ℕ)).d n (n + 1) z) (n + 1) := by
  have h : ∀ k, k ≤ n + 1 → ∃ z : (K.total (.up ℕ)).X n,
      CycleNormalization.ZeroRowsBefore K (n + 1)
        (x - (K.total (.up ℕ)).d n (n + 1) z) k := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨0, ?_⟩
        intro a b hab ha
        omega
    | succ k ih =>
        intro hk
        obtain ⟨z, hz⟩ := ih (by omega)
        have himage' : CycleNormalization.ZeroRowsBefore K (n + 2)
            ((K.total (.up ℕ)).d (n + 1) (n + 2)
              (x - (K.total (.up ℕ)).d n (n + 1) z)) (k + 1) := by
          rw [total_sub_boundary_d]
          exact zeroRowsBefore_mono K himage hk
        obtain ⟨w, hw⟩ := exists_remove_row_of_image_zero_of_lt K n k (by omega)
          (x - (K.total (.up ℕ)).d n (n + 1) z) hz himage' hrows
        refine ⟨z + w, ?_⟩
        have heq : x - (K.total (.up ℕ)).d n (n + 1) (z + w) =
            (x - (K.total (.up ℕ)).d n (n + 1) z) -
              (K.total (.up ℕ)).d n (n + 1) w := by
          rw [map_add]
          abel
        rw [heq]
        exact hw
  exact h (n + 1) le_rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.FilteredNormalization
