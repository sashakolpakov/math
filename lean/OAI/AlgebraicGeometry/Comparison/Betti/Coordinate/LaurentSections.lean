import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.CoordinateSplit

/-! # Laurent Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentSections.Dolbeault

noncomputable section

/-! Laurent splitting in one chosen coordinate of a genuine finite coordinate
product, with holomorphic dependence on every remaining coordinate. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι] (U : ι → Opens ℂ) (i : ι)

def filledCoordinatePoint (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤) :=
  (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤).symm
    ⟨(Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen x).val,
      ⟨(Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen x).property.1, trivial⟩⟩

def invertedCoordinatePoint (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤) :=
  (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤).symm
    ⟨((Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen x).val.1,
      (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen x).val.2⁻¹),
      ⟨(Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen x).property.1, trivial⟩⟩

theorem filledCoordinatePoint_val (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    (filledCoordinatePoint U i x).val = x.val :=
  (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm_apply_apply x.val

theorem invertedCoordinatePoint_same (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    (invertedCoordinatePoint U i x).val i = (x.val i)⁻¹ :=
  DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_same i _

theorem invertedCoordinatePoint_other (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen))
    (j : ι) (hj : j ≠ i) : (invertedCoordinatePoint U i x).val j = x.val j :=
  DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_other i _ j hj

def coordinatePositiveLaurentSectionMap :
    Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) :=
  (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i ⊤).symm.toLinearEquiv.toLinearMap.comp
    ((Laurent.FiberVanishing.Dolbeault.positiveLaurentSectionMap (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j))).comp
      (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen).toLinearEquiv.toLinearMap)

def coordinateNegativeLaurentSectionMap :
    Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) →ₗ[ℂ]
      Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) :=
  (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i ⊤).symm.toLinearEquiv.toLinearMap.comp
    ((Laurent.FiberVanishing.Dolbeault.negativeLaurentSectionMap (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j))).comp
      (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen).toLinearEquiv.toLinearMap)

theorem coordinateNegativeLaurentSection_zero
    (f : Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)))
    (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i ⊤)) (hx : x.val i = 0) :
    (coordinateNegativeLaurentSectionMap U i f).val x = 0 := by
  change Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart (fun z => Laurent.FiberVanishing.Dolbeault.holomorphicFunctionExtension _
    (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen f)
    ((fun j : {j : ι // j ≠ i} => x.val j), z)) (x.val i) = 0
  rw [hx]
  exact Holomorphic.LaurentSplitting.Dolbeault.negativeLaurentPart_zero _

theorem coordinateLaurentSections_identity
    (f : Holomorphic.FunctionPure.holomorphicFunctions (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)))
    (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i PuncturedCauchy.Dolbeault.puncturedComplexOpen)) :
    (coordinatePositiveLaurentSectionMap U i f).val (filledCoordinatePoint U i x) +
      (coordinateNegativeLaurentSectionMap U i f).val (invertedCoordinatePoint U i x) = f.val x := by
  change (Laurent.FiberVanishing.Dolbeault.positiveLaurentSection (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j))
      (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen f)).val
      (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤ (filledCoordinatePoint U i x)) +
    (Laurent.FiberVanishing.Dolbeault.negativeLaurentSection (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j))
      (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen f)).val
      (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i ⊤ (invertedCoordinatePoint U i x)) = _
  rw [filledCoordinatePoint, invertedCoordinatePoint, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  exact (Laurent.FiberVanishing.Dolbeault.laurentSectionSplitting_identity (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j))
    (Holomorphic.CoordinateSplit.Dolbeault.coordinateHolomorphicSectionEquiv U i PuncturedCauchy.Dolbeault.puncturedComplexOpen f)
    (Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen x)).trans
      (congrArg f.val ((Holomorphic.CoordinateSplit.Dolbeault.coordinatePolydiscSplitHomeomorph U i PuncturedCauchy.Dolbeault.puncturedComplexOpen).symm_apply_apply x))

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LaurentSections.Dolbeault
