import OAI.AlgebraicGeometry.DivisorClass.Chern.Positive.ComplexCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.DiskGenerator

/-! # Line Product Coordinates -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LineProductCoordinates

noncomputable section

/-! Complex-linear concatenation places the original complex line first,
followed by the tangent coordinates, with their internal order preserved. -/

open _root_.CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def complexLineProductCoordinates (d : ℕ) :
    ((Fin 1 → ℂ) × (Fin d → ℂ)) ≃L[ℂ] (Fin (d + 1) → ℂ) :=
  ((ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ).prodCongr
    (ContinuousLinearEquiv.refl ℂ (Fin d → ℂ))).trans
      (Fin.consEquivL ℂ (fun _ : Fin (d + 1) => ℂ))

theorem complexLineProductCoordinates_zero (d : ℕ) (x : Fin 1 → ℂ) (y : Fin d → ℂ) :
    complexLineProductCoordinates d (x, y) 0 = x 0 := rfl

theorem complexLineProductCoordinates_succ (d : ℕ) (x : Fin 1 → ℂ) (y : Fin d → ℂ) (i : Fin d) :
    complexLineProductCoordinates d (x, y) i.succ = y i := rfl

theorem complexRealEuclideanEquiv_apply_index (d : ℕ) (x : Fin d → ℂ)
    (i : Fin d) (j : Fin 2) :
    CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv d x ⟨2 * i.val + j.val, by omega⟩ =
      CycleClass.Geometric.RealComplexNormalModel.Cycles.complexCoordinatePair (x i) j := by
  have hi : (⟨2 * i.val + j.val, by omega⟩ : Fin (2 * d)) = CycleClass.Geometric.RealComplexNormalModel.Cycles.complexInterleavedIndex d (i, j) := by
    apply Fin.ext
    exact (CycleClass.Geometric.RealComplexNormalModel.Cycles.complexInterleavedIndex_val d i j).symm
  rw [hi, CycleClass.Geometric.RealComplexNormalModel.Cycles.complexRealEuclideanEquiv_apply_pair]

theorem positiveComplexRealCoordinates_apply_index (p : ℕ) (x : Fin (p + 1) → ℂ)
    (i : Fin (p + 1)) (j : Fin 2) :
    Positive.ComplexCoordinates.positiveComplexRealCoordinates p x ⟨2 * i.val + j.val, by omega⟩ =
      CycleClass.Geometric.RealComplexNormalModel.Cycles.complexCoordinatePair (x i) j := by
  simpa only [Positive.ComplexCoordinates.positiveComplexRealCoordinates, Nat.mul_succ, id_eq] using
    complexRealEuclideanEquiv_apply_index (p + 1) x i j

theorem positiveComplexRealCoordinates_head (p : ℕ) (x : Fin 1 → ℂ) (y : Fin (p + 1) → ℂ)
    (j : Fin 2) :
    Positive.ComplexCoordinates.positiveComplexRealCoordinates (p + 1) (complexLineProductCoordinates (p + 1) (x, y))
      ⟨j.val, by omega⟩ = CycleClass.Geometric.RealComplexNormalModel.Cycles.complexCoordinatePair (x 0) j := by
  have h := positiveComplexRealCoordinates_apply_index (p + 1)
    (complexLineProductCoordinates (p + 1) (x, y)) 0 j
  simpa only [Fin.val_zero, mul_zero, zero_add, complexLineProductCoordinates_zero] using h

theorem positiveComplexRealCoordinates_tail (p : ℕ) (x : Fin 1 → ℂ) (y : Fin (p + 1) → ℂ)
    (k : Fin (2 * p + 2)) :
    Positive.ComplexCoordinates.positiveComplexRealCoordinates (p + 1) (complexLineProductCoordinates (p + 1) (x, y))
      ⟨k.val + 2, by omega⟩ = Positive.ComplexCoordinates.positiveComplexRealCoordinates p y k := by
  let i : Fin (p + 1) := ⟨k.val / 2, by omega⟩
  let j : Fin 2 := ⟨k.val % 2, Nat.mod_lt _ (by decide)⟩
  have hk : k = ⟨2 * i.val + j.val, by omega⟩ := by
    apply Fin.ext
    dsimp [i, j]
    omega
  have hs : (⟨k.val + 2, by omega⟩ : Fin (2 * (p + 1) + 2)) =
      ⟨2 * i.succ.val + j.val, by omega⟩ := by
    apply Fin.ext
    dsimp [i, j]
    omega
  rw [hs, positiveComplexRealCoordinates_apply_index, complexLineProductCoordinates_succ]
  exact (positiveComplexRealCoordinates_apply_index p y i j).symm.trans
    (congrArg (fun a => Positive.ComplexCoordinates.positiveComplexRealCoordinates p y a) hk.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.LineProductCoordinates
