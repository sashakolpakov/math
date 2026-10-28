import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.CycleNormalization
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.HorizontalEdge

/-! # Row -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.Row

noncomputable section

/-! Recovering a normalized total cycle from the augmented complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- An element with all earlier rows zero is its final-coordinate inclusion. -/
theorem total_eq_final_coordinate (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (hbefore : CycleNormalization.ZeroRowsBefore K n x n) :
    K.ιTotal (.up ℕ) n 0 n rfl (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n x) = x := by
  have h : ∀ a b, a + b = n →
      FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K a b n (K.ιTotal (.up ℕ) n 0 n rfl
        (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n x)) = FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K a b n x := by
    intro a b hab
    by_cases ha : a = n
    · have hb : b = 0 := by omega
      subst a b
      change (K.ιTotal (.up ℕ) n 0 n rfl ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n)
        (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n x) = FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n x
      simp
    · have hn : n ≠ a := Ne.symm ha
      rw [hbefore a b hab (by omega)]
      change (K.ιTotal (.up ℕ) n 0 n rfl ≫ FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K a b n)
        (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n x) = 0
      simp [hn]
  apply (ElementCoordinates.totalCoordinateAddEquiv K n).injective
  funext i
  exact h i (n - i) (by omega)

/-- The final coordinate of a total cycle is a column cycle. -/
theorem total_cycle_final_column (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (hx : (K.total (.up ℕ)).d n (n + 1) x = 0) :
    (K.d n (n + 1)).f 0 (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K n 0 n x) = 0 := by
  have h := congrArg (fun f => f x) (BoundaryCoordinates.total_d_π_zero_right K n)
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h.symm

/-- A total cycle lifts, modulo an actual boundary, to a cycle in the augmented complex. -/
theorem exists_horizontal_cycle_lift
    (A : CochainComplex AddCommGrpCat.{u} ℕ)
    (e : ∀ q, A.X q ⟶ (K.X q).X 0)
    (he : ∀ q q', (ComplexShape.up ℕ).Rel q q' →
      e q ≫ (K.d q q').f 0 = A.d q q' ≫ e q')
    (w : ∀ q, e q ≫ (K.X q).d 0 1 = 0)
    (haug : ∀ q, (ShortComplex.mk (e q) ((K.X q).d 0 1) (w q)).Exact)
    (hmono : ∀ q, Mono (e q)) (hrows : CycleNormalization.RowsExact K)
    (n : ℕ) (x : (K.total (.up ℕ)).X (n + 1))
    (hx : (K.total (.up ℕ)).d (n + 1) (n + 2) x = 0) :
    ∃ a : A.X (n + 1), A.d (n + 1) (n + 2) a = 0 ∧
      ∃ z : (K.total (.up ℕ)).X n,
        (HorizontalEdge.totalUpNatHorizontalEdge K A e he w).f (n + 1) a =
          x - (K.total (.up ℕ)).d n (n + 1) z := by
  obtain ⟨z, hz⟩ := CycleNormalization.exists_normalize_total_cycle K n x hx hrows
  let y := x - (K.total (.up ℕ)).d n (n + 1) z
  have hy : (K.total (.up ℕ)).d (n + 1) (n + 2) y = 0 :=
    CycleNormalization.total_sub_boundary_cycle K n x hx z
  have hrow := CycleNormalization.total_cycle_row_of_zero_before K (n + 1) (n + 1) 0 rfl y hy hz
  obtain ⟨a, ha⟩ := (ShortComplex.ab_exact_iff _).mp (haug (n + 1)) _ hrow
  have hacycle : A.d (n + 1) (n + 2) a = 0 := by
    apply (AddCommGrpCat.mono_iff_injective (e (n + 2))).mp (hmono (n + 2))
    rw [map_zero]
    have heval := ConcreteCategory.congr_hom (he (n + 1) (n + 2) rfl) a
    have hcol := total_cycle_final_column K (n + 1) y hy
    rw [← ha] at hcol
    exact heval.symm.trans hcol
  refine ⟨a, hacycle, z, ?_⟩
  change K.ιTotal (.up ℕ) (n + 1) 0 (n + 1) rfl (e (n + 1) a) = y
  rw [ha]
  exact total_eq_final_coordinate K (n + 1) y hz

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.Row
