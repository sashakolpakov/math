import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.CoordinateSplit

/-! # Coordinate Polydisc Update -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscUpdate

noncomputable section

/-! Shrinking exactly one coordinate domain in an actual finite polydisc. -/

open _root_.TopologicalSpace Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coordinatePolydisc_update_le (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ) (hW : W ≤ U i) :
    Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W) ≤ Complex.CoordinateSplit.coordinatePolydisc U := by
  intro x hx
  apply (Complex.CoordinateSplit.mem_coordinatePolydisc U x).mpr
  intro j
  have hj := (Complex.CoordinateSplit.mem_coordinatePolydisc _ x).mp hx j
  by_cases h : j = i
  · subst j
    exact hW (by simpa only [Function.update_self] using hj)
  · simpa only [Function.update_of_ne h] using hj

theorem coordinatePolydisc_update_mem (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ)
    (x : ι → ℂ) (hx : x ∈ Complex.CoordinateSplit.coordinatePolydisc U) (hW : x i ∈ W) :
    x ∈ Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W) := by
  apply (Complex.CoordinateSplit.mem_coordinatePolydisc _ x).mpr
  intro j
  by_cases h : j = i
  · subst j
    simpa only [Function.update_self] using hW
  · simpa only [Function.update_of_ne h] using (Complex.CoordinateSplit.mem_coordinatePolydisc U x).mp hx j

theorem splitComplexCoordinate_update_mapsTo (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ) :
    MapsTo (Complex.CoordinateSplit.splitComplexCoordinate i) (Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W) : Set (ι → ℂ))
      (OneFormCauchyElimination.complexProductOpen (Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W :
        Set (({j : ι // j ≠ i} → ℂ) × ℂ)) := by
  have hother : (fun j : {j : ι // j ≠ i} => Function.update U i W j) = (fun j : {j : ι // j ≠ i} => U j) := by
    funext j
    exact Function.update_of_ne j.property _ _
  simpa only [hother, Function.update_self] using Complex.CoordinateSplit.splitComplexCoordinate_mapsTo (Function.update U i W) i

theorem splitComplexCoordinate_update_symm_mapsTo (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ) :
    MapsTo (Complex.CoordinateSplit.splitComplexCoordinate i).symm
      (OneFormCauchyElimination.complexProductOpen (Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W :
        Set (({j : ι // j ≠ i} → ℂ) × ℂ)) (Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W) : Set (ι → ℂ)) := by
  have hother : (fun j : {j : ι // j ≠ i} => Function.update U i W j) = (fun j : {j : ι // j ≠ i} => U j) := by
    funext j
    exact Function.update_of_ne j.property _ _
  simpa only [hother, Function.update_self] using Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo (Function.update U i W) i

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscUpdate
