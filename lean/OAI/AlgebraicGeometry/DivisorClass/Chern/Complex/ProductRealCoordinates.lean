import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LineProductCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.PlaneProductCharts

/-! # Product Real Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ProductRealCoordinates

noncomputable section

/-! The actual complex-linear concatenation is exactly the ordered plane
product in the original real coordinates. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def combinedComplexRealCoordinates (p : ℕ) :
    (Fin (p + 2) → ℂ) ≃L[ℝ] EuclideanSpace ℝ (Fin (2 * p + 4)) := by
  simpa only [Nat.mul_succ] using Positive.ComplexCoordinates.positiveComplexRealCoordinates (p + 1)

theorem combinedComplexRealCoordinates_head (p : ℕ) (x : Fin 1 → ℂ) (y : Fin (p + 1) → ℂ)
    (j : Fin 2) :
    combinedComplexRealCoordinates p (LineProductCoordinates.complexLineProductCoordinates (p + 1) (x, y))
      ⟨j.val, by omega⟩ = CycleClass.Geometric.RealComplexNormalModel.Cycles.complexCoordinatePair (x 0) j := by
  simpa only [combinedComplexRealCoordinates, Nat.mul_succ, id_eq] using
    LineProductCoordinates.positiveComplexRealCoordinates_head p x y j

theorem combinedComplexRealCoordinates_tail (p : ℕ) (x : Fin 1 → ℂ) (y : Fin (p + 1) → ℂ)
    (k : Fin (2 * p + 2)) :
    combinedComplexRealCoordinates p (LineProductCoordinates.complexLineProductCoordinates (p + 1) (x, y))
      k.succ.succ = Positive.ComplexCoordinates.positiveComplexRealCoordinates p y k := by
  have h : combinedComplexRealCoordinates p (LineProductCoordinates.complexLineProductCoordinates (p + 1) (x, y))
      ⟨k.val + 2, by omega⟩ = Positive.ComplexCoordinates.positiveComplexRealCoordinates p y k := by
    simpa only [combinedComplexRealCoordinates, Nat.mul_succ, id_eq] using
      LineProductCoordinates.positiveComplexRealCoordinates_tail p x y k
  have hi : k.succ.succ = (⟨k.val + 2, by omega⟩ : Fin (2 * p + 4)) := by
    apply Fin.ext
    rfl
  exact (congrArg (fun i => combinedComplexRealCoordinates p
    (LineProductCoordinates.complexLineProductCoordinates (p + 1) (x, y)) i) hi).trans h

theorem complexLineProductCoordinates_real (p : ℕ) (x : Fin 1 → ℂ) (y : Fin (p + 1) → ℂ) :
    combinedComplexRealCoordinates p (LineProductCoordinates.complexLineProductCoordinates (p + 1) (x, y)) =
      PlaneProductCharts.planeProductCoordinates (2 * p + 2) (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1 x, Positive.ComplexCoordinates.positiveComplexRealCoordinates p y) := by
  ext k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun i => ?_) j) k
  · exact (combinedComplexRealCoordinates_head p x y 0).trans
      (LineProductCoordinates.complexRealEuclideanEquiv_apply_index 1 x 0 0).symm
  · exact (combinedComplexRealCoordinates_head p x y 1).trans
      (LineProductCoordinates.complexRealEuclideanEquiv_apply_index 1 x 0 1).symm
  · exact combinedComplexRealCoordinates_tail p x y i

def complexLineProductRealCoordinates (d : ℕ) :
    ((Fin 1 → ℂ) × (Fin d → ℂ)) ≃L[ℝ] (Fin (d + 1) → ℂ) where
  toLinearEquiv := (LineProductCoordinates.complexLineProductCoordinates d).toLinearEquiv.restrictScalars ℝ
  continuous_toFun := (LineProductCoordinates.complexLineProductCoordinates d).continuous
  continuous_invFun := (LineProductCoordinates.complexLineProductCoordinates d).symm.continuous

def fullPlaneProductComplexCoordinates (p : ℕ) :
    (PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2))) ≃L[ℝ] (Fin (p + 2) → ℂ) :=
  (((CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).symm).prodCongr (Positive.ComplexCoordinates.positiveComplexRealCoordinates p).symm).trans
    (complexLineProductRealCoordinates (p + 1))

theorem fullPlaneProductComplexCoordinates_real (p : ℕ)
    (v : PlaneHalf.CoordinatePlane × EuclideanSpace ℝ (Fin (2 * p + 2))) :
    combinedComplexRealCoordinates p (fullPlaneProductComplexCoordinates p v) =
      PlaneProductCharts.planeProductCoordinates (2 * p + 2) v := by
  change combinedComplexRealCoordinates p
    (LineProductCoordinates.complexLineProductCoordinates (p + 1)
      ((CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv 1).symm v.1, (Positive.ComplexCoordinates.positiveComplexRealCoordinates p).symm v.2)) = _
  rw [complexLineProductCoordinates_real, ContinuousLinearEquiv.apply_symm_apply,
    ContinuousLinearEquiv.apply_symm_apply]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ProductRealCoordinates
