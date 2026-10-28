import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentSections
import OAI.AlgebraicGeometry.Comparison.Betti.Laurent.FiberVanishing

/-! # Laurent Vanishing -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentVanishing.Dolbeault

noncomputable section

/-! Splitting one coordinate preserves vanishing on every other coordinate
hyperplane, as required when iterating the normalized Laurent decomposition. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Opens ℂ) (i : ι)

def coordinateSlicePoint (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) (z : ℂ) (hz : z ≠ 0) :
    DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen) :=
  (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen).symm
    ⟨((Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤ x).val.1, z),
      ⟨(Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤ x).property.1, hz⟩⟩

theorem coordinateSlicePoint_other (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤))
    (z : ℂ) (hz : z ≠ 0) (j : ι) (hj : j ≠ i) :
    (coordinateSlicePoint U i x z hz).val j = x.val j :=
  DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_other i _ j hj

theorem coordinateLaurentSections_preserve_zero
    (f : Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)))
    (j : ι) (hj : j ≠ i)
    (hf : ∀ x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen), x.val j = 0 → f.val x = 0)
    (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) (hx : x.val j = 0) :
    (LaurentSections.Dolbeault.coordinatePositiveLaurentSectionMap U i f).val x = 0 ∧
      (LaurentSections.Dolbeault.coordinateNegativeLaurentSectionMap U i f).val x = 0 := by
  let S := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun k : {k : ι // k ≠ i} => U k)
  let p : S := ⟨(Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤ x).val.1,
    (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤ x).property.1⟩
  let g := Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen f
  have h : ∀ z : ℂ, ∀ hz : z ≠ 0, g.val ⟨(p.val, z), ⟨p.property, hz⟩⟩ = 0 := by
    intro z hz
    change f.val (coordinateSlicePoint U i x z hz) = 0
    exact hf _ ((coordinateSlicePoint_other U i x z hz j hj).trans hx)
  exact Laurent.FiberVanishing.Dolbeault.laurentSection_fiber_zero S g p h (x.val i)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentVanishing.Dolbeault
