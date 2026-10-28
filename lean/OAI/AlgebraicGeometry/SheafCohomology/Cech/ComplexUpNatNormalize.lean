import OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatElimination

/-! # Complex Up Nat Normalize -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatNormalize.Projective

noncomputable section

/-! Normalizing total cycles one row at a time. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- All coordinates in rows before `k` vanish. -/
def ZeroRowsBefore (n : ℕ) (x : (K.total (.up ℕ)).X n) (k : ℕ) : Prop :=
  ∀ a b, a + b = n → a < k → (UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) a b n x = 0

/-- Subtracting a total boundary preserves being a cycle. -/
theorem total_sub_boundary_cycle (n : ℕ) (x : (K.total (.up ℕ)).X (n + 1))
    (hx : (K.total (.up ℕ)).d (n + 1) (n + 2) x = 0)
    (z : (K.total (.up ℕ)).X n) :
    (K.total (.up ℕ)).d (n + 1) (n + 2)
      (x - (K.total (.up ℕ)).d n (n + 1) z) = 0 := by
  rw [map_sub, hx]
  have hz : (K.total (.up ℕ)).d (n + 1) (n + 2)
      ((K.total (.up ℕ)).d n (n + 1) z) = 0 := by
    change ((K.total (.up ℕ)).d n (n + 1) ≫
      (K.total (.up ℕ)).d (n + 1) (n + 2)) z = 0
    rw [(K.total (.up ℕ)).d_comp_d]
    rfl
  rw [hz, sub_self]

/-- The first potentially nonzero row coordinate of a total cycle is a row cycle. -/
theorem total_cycle_row_of_zero_before (n q p : ℕ) (hdeg : q + p = n)
    (x : (K.total (.up ℕ)).X n)
    (hx : (K.total (.up ℕ)).d n (n + 1) x = 0)
    (hbefore : ZeroRowsBefore K n x q) :
    (K.X q).d p (p + 1) ((UpNatLowDegrees.HomologicalComplex₂.πTotalUpNat K) q p n x) = 0 := by
  cases q with
  | zero =>
      have hn : p = n := by omega
      clear hdeg
      subst n
      exact ComplexUpNatCycles.Projective.total_cycle_zero_row K p x hx
  | succ q =>
      have hn : q + p + 1 = n := by omega
      clear hdeg
      subst n
      apply ComplexUpNatCycles.Projective.total_cycle_row_of_previous_zero K q p x hx
      exact hbefore q (p + 1) (by omega) (by omega)

/-- Exactness of the next row gives one more vanished coordinate, without changing
the cohomology class of the total cycle. -/
theorem exists_remove_next_row (q p : ℕ)
    (x : (K.total (.up ℕ)).X (q + p + 1))
    (hx : (K.total (.up ℕ)).d (q + p + 1) (q + p + 2) x = 0)
    (hbefore : ZeroRowsBefore K (q + p + 1) x q)
    (hrow : (ShortComplex.mk ((K.X q).d p (p + 1))
      ((K.X q).d (p + 1) (p + 2)) ((K.X q).d_comp_d p (p + 1) (p + 2))).Exact) :
    ∃ z : (K.total (.up ℕ)).X (q + p),
      ZeroRowsBefore K (q + p + 1)
        (x - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) (q + 1) ∧
      (K.total (.up ℕ)).d (q + p + 1) (q + p + 2)
        (x - (K.total (.up ℕ)).d (q + p) (q + p + 1) z) = 0 := by
  have hc := total_cycle_row_of_zero_before K (q + p + 1) q (p + 1)
    (by omega) x hx hbefore
  obtain ⟨z, hz, hpreserve⟩ := ComplexUpNatElimination.Projective.exists_remove_row_coordinate K q p x hrow hc
  refine ⟨z, ?_, total_sub_boundary_cycle K (q + p) x hx z⟩
  intro a b hab ha
  by_cases haq : a < q
  · rw [hpreserve a b haq]
    exact hbefore a b hab haq
  · have heqa : a = q := by omega
    have heqb : b = p + 1 := by omega
    subst a b
    exact hz

/-- Every row is exact in positive horizontal degrees. -/
def RowsExact : Prop := ∀ q p,
  (ShortComplex.mk ((K.X q).d p (p + 1)) ((K.X q).d (p + 1) (p + 2))
    ((K.X q).d_comp_d p (p + 1) (p + 2))).Exact

/-- Row elimination with the total degree kept fixed. -/
theorem exists_remove_next_row_of_lt (n q : ℕ) (hq : q < n + 1)
    (x : (K.total (.up ℕ)).X (n + 1))
    (hx : (K.total (.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hbefore : ZeroRowsBefore K (n + 1) x q) (hrows : RowsExact K) :
    ∃ z : (K.total (.up ℕ)).X n,
      ZeroRowsBefore K (n + 1)
        (x - (K.total (.up ℕ)).d n (n + 1) z) (q + 1) ∧
      (K.total (.up ℕ)).d (n + 1) (n + 2)
        (x - (K.total (.up ℕ)).d n (n + 1) z) = 0 := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hq)
  exact exists_remove_next_row K q p x hx hbefore (hrows q p)

/-- Every positive-degree total cycle can be normalized to the final row by subtracting
a boundary. This is the finite row-elimination argument in arbitrary degree. -/
theorem exists_normalize_total_cycle (n : ℕ)
    (x : (K.total (.up ℕ)).X (n + 1))
    (hx : (K.total (.up ℕ)).d (n + 1) (n + 2) x = 0)
    (hrows : RowsExact K) :
    ∃ z : (K.total (.up ℕ)).X n,
      ZeroRowsBefore K (n + 1)
        (x - (K.total (.up ℕ)).d n (n + 1) z) (n + 1) := by
  have h : ∀ k, k ≤ n + 1 → ∃ z : (K.total (.up ℕ)).X n,
      ZeroRowsBefore K (n + 1)
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
        have hc := total_sub_boundary_cycle K n x hx z
        obtain ⟨w, hw, _⟩ := exists_remove_next_row_of_lt K n k (by omega)
          (x - (K.total (.up ℕ)).d n (n + 1) z) hc hz hrows
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

end OAI.AlgebraicGeometry.SheafCohomology.Cech.ComplexUpNatNormalize.Projective
