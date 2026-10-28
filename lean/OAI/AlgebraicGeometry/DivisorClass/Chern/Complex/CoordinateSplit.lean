import OAI.AlgebraicGeometry.DivisorClass.Chern.OneFormCauchyElimination
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Coordinate Split -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CoordinateSplit

noncomputable section

/-! Actual complex-linear coordinate splitting and its product of open coordinate domains. -/

open _root_.TopologicalSpace Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def splitComplexCoordinateLinear (i : ι) :
    (ι → ℂ) ≃ₗ[ℂ] (({j : ι // j ≠ i} → ℂ) × ℂ) where
  toFun x := (fun j => x j, x i)
  invFun q j := if h : j = i then q.2 else q.1 ⟨j, h⟩
  left_inv x := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv q := by
    apply Prod.ext
    · funext j
      simp [j.property]
    · simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def splitComplexCoordinate (i : ι) :
    (ι → ℂ) ≃L[ℂ] (({j : ι // j ≠ i} → ℂ) × ℂ) :=
  (splitComplexCoordinateLinear i).toContinuousLinearEquiv

theorem splitComplexCoordinate_apply (i : ι) (x : ι → ℂ) :
    splitComplexCoordinate i x = (fun j : {j : ι // j ≠ i} => x j, x i) := rfl

theorem splitComplexCoordinate_symm_same (i : ι) (q : ({j : ι // j ≠ i} → ℂ) × ℂ) :
    (splitComplexCoordinate i).symm q i = q.2 := by
  simp [splitComplexCoordinate, splitComplexCoordinateLinear]

theorem splitComplexCoordinate_symm_other (i : ι) (q : ({j : ι // j ≠ i} → ℂ) × ℂ)
    (j : ι) (hj : j ≠ i) : (splitComplexCoordinate i).symm q j = q.1 ⟨j, hj⟩ := by
  simp [splitComplexCoordinate, splitComplexCoordinateLinear, hj]

def coordinatePolydisc (U : ι → Opens ℂ) : Opens (ι → ℂ) :=
  ⟨⋂ i, (fun x : ι → ℂ => x i) ⁻¹' (U i : Set ℂ),
    isOpen_iInter_of_finite (fun i => (U i).isOpen.preimage (continuous_apply i))⟩

omit [DecidableEq ι] in
theorem mem_coordinatePolydisc (U : ι → Opens ℂ) (x : ι → ℂ) :
    x ∈ coordinatePolydisc U ↔ ∀ i, x i ∈ U i := by
  simp [coordinatePolydisc]

theorem splitComplexCoordinate_mapsTo (U : ι → Opens ℂ) (i : ι) :
    MapsTo (splitComplexCoordinate i) (coordinatePolydisc U : Set (ι → ℂ))
      (OneFormCauchyElimination.complexProductOpen (coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i) :
        Set (({j : ι // j ≠ i} → ℂ) × ℂ)) := by
  intro x hx
  have hx' := (mem_coordinatePolydisc U x).mp hx
  exact ⟨(mem_coordinatePolydisc _ _).mpr (fun j => hx' j), hx' i⟩

theorem splitComplexCoordinate_symm_mapsTo (U : ι → Opens ℂ) (i : ι) :
    MapsTo (splitComplexCoordinate i).symm
      (OneFormCauchyElimination.complexProductOpen (coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i) :
        Set (({j : ι // j ≠ i} → ℂ) × ℂ)) (coordinatePolydisc U : Set (ι → ℂ)) := by
  intro q hq
  apply (mem_coordinatePolydisc U _).mpr
  intro j
  by_cases hj : j = i
  · subst j
    rw [splitComplexCoordinate_symm_same]
    exact hq.2
  · rw [splitComplexCoordinate_symm_other i q j hj]
    exact (mem_coordinatePolydisc _ _).mp hq.1 ⟨j, hj⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CoordinateSplit
