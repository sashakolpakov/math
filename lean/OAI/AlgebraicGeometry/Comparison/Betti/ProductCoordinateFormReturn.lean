import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionTransport
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare
import OAI.AlgebraicGeometry.Comparison.Betti.ContractionCauchyPrimitive

/-! # Product Coordinate Form Return -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateFormReturn.Dolbeault

noncomputable section

/-! Exact return along the selected-coordinate split, keeping every
original coordinate domain fixed. -/

open _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

def productCoordinateFormReturn (U : ι → Opens ℂ) (i : ι) :
    Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i)) n →ₗ[ℂ]
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) n :=
  DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i)

theorem productCoordinateFormReturn_inverse (U : ι → Opens ℂ) (i : ι)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) n) :
    productCoordinateFormReturn U i (DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormToProduct U i a) = a :=
  DivisorClass.Chern.Complex.LinearPullbackLaws.complexLinearOpenPullback_inverse
    (U := ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i))
    (V := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i) a

theorem productCoordinateFormReturn_d (U : ι → Opens ℂ) (i : ι)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i)) n) :
    productCoordinateFormReturn U i (DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n a) =
      DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n (productCoordinateFormReturn U i a) :=
  (DivisorClass.Chern.Complex.LinearOpenPullback.openDolbeaultD_complexLinearPullback _ _ a).symm

theorem productCoordinateFormReturn_closed (U : ι → Opens ℂ) (i : ι)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i)) n)
    (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n a = 0) : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n (productCoordinateFormReturn U i a) = 0 :=
  DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_closed (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i) a ha

theorem productCoordinateFormReturn_coefficient (U : ι → Opens ℂ) (i : ι)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) (U i)) 1)
    (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (v : ι → ℂ) :
    DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (productCoordinateFormReturn U i a x) v =
      DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (a ⟨DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i x, DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i x.property⟩)
        (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i v) :=
  DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_oneFormCoefficient (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i) a x v

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateFormReturn.Dolbeault
