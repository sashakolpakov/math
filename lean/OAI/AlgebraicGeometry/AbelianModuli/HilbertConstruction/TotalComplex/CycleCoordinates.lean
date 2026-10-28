import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.ElementCoordinates

/-! # Cycle Coordinates -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.CycleCoordinates

noncomputable section

/-! Cycle equations for finite bidegree coordinates of the actual total complex. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.Preadditive

universe u

variable (K : HomologicalComplex₂ AddCommGrpCat.{u} (.up ℕ) (.up ℕ))
    [K.HasTotal (.up ℕ)]

/-- The first row coordinate of a total cycle is a row cycle. -/
theorem total_cycle_zero_row (n : ℕ) (x : (K.total (.up ℕ)).X n)
    (hx : (K.total (.up ℕ)).d n (n + 1) x = 0) :
    (K.X 0).d n (n + 1) (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K 0 n n x) = 0 := by
  have h := congrArg (fun f => f x) (BoundaryCoordinates.total_d_π_zero K n)
  simpa only [ConcreteCategory.comp_apply, hx, map_zero] using h.symm

/-- Interior coordinates of a total cycle satisfy the signed adjacent-coordinate equation. -/
theorem total_cycle_interior (q p : ℕ)
    (x : (K.total (.up ℕ)).X (q + p + 1))
    (hx : (K.total (.up ℕ)).d (q + p + 1) (q + p + 1 + 1) x = 0) :
    (K.d q (q + 1)).f (p + 1) (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K q (p + 1) (q + p + 1) x) +
      ((-1 : ℤˣ) ^ (q + 1)) •
        (K.X (q + 1)).d p (p + 1) (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (q + 1) p (q + p + 1) x) = 0 := by
  have h := congrArg (fun f => f x) (BoundaryCoordinates.total_d_π_interior K q p)
  simpa [ConcreteCategory.comp_apply, hx, Units.smul_def] using h.symm

/-- Once the preceding coordinate has vanished, the next coordinate of a total cycle
is itself a row cycle. This is the induction step used before choosing a row preimage. -/
theorem total_cycle_row_of_previous_zero (q p : ℕ)
    (x : (K.total (.up ℕ)).X (q + p + 1))
    (hx : (K.total (.up ℕ)).d (q + p + 1) (q + p + 1 + 1) x = 0)
    (hprev : FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K q (p + 1) (q + p + 1) x = 0) :
    (K.X (q + 1)).d p (p + 1) (FirstQuadrantTotalCoordinates.TotalComplex.πTotalUpNat K (q + 1) p (q + p + 1) x) = 0 := by
  have h := total_cycle_interior K q p x hx
  rw [hprev, map_zero, zero_add] at h
  exact (smul_eq_zero_iff_eq _).mp h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TotalComplex.CycleCoordinates
