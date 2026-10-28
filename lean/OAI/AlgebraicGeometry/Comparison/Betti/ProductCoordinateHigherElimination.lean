import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineHigherFormElimination
import OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateFormReturn
import OAI.AlgebraicGeometry.Comparison.Betti.PolydiscCoefficientElimination

/-! # Product Coordinate Higher Elimination -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateHigherElimination.Dolbeault

noncomputable section

/-! Global elimination of a chosen antiholomorphic coordinate on a
product of ordinary and punctured complex lines. -/

open _root_.TopologicalSpace Set

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def coordinateLineProduct (ε : ι → Bool) : Opens (ι → ℂ) :=
  DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun i => PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen (ε i))

theorem exists_product_coordinate_higherForm_elimination (ε : ι → Bool)
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (coordinateLineProduct ε) (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (i : ι) :
    ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (coordinateLineProduct ε) (n + 2),
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (coordinateLineProduct ε) (n + 1),
      b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = a ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) b = 0 ∧
        DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) b ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
        Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) b = 0 ∧
        (∀ j : ι, j ≠ i → Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) a = 0 →
          Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) b = 0) := by
  let U := fun j => PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen (ε j)
  let S := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)
  let A := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormToProduct U i a
  have hA : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) A = 0 := DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_closed
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) a ha
  have hAp : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) A := DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) hpure
  obtain ⟨u, hup, hB, hBp, hBi, hBprior⟩ :=
    Coordinate.LineHigherFormElimination.Dolbeault.exists_coordinateLine_higherForm_coefficient_elimination S (ε i) n p q hn A hA hAp
  let B := Open.DolbeaultCorrection.correctOpenDolbeaultForm (n + 1) A u
  let b := ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i B
  let t := ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i u
  have hsum : b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = a := by
    have hs := congrArg (ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i)
      (PolydiscCoefficientElimination.Dolbeault.correctOpenDolbeaultForm_add_dbar (n + 1) A u)
    erw [(ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i).map_add, ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_d] at hs
    exact hs.trans (ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_inverse U i a)
  refine ⟨b, t, hsum, ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_closed U i B hB,
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i) hBp,
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i) hup, ?_, ?_⟩
  · apply Open.ContractionPullback.Dolbeault.openAntiContraction_pullback_zero
    change Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i)) B = 0
    rw [DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_same]
    exact hBi
  · intro j hji hj
    apply Open.ContractionPullback.Dolbeault.openAntiContraction_pullback_zero
    change Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j)) B = 0
    rw [DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji]
    apply hBprior
    apply Open.ContractionPullback.Dolbeault.openAntiContraction_pullback_zero
    change Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) ((DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm
      ((fun k : {k : ι // k ≠ i} => DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j k), 0)) a = 0
    rw [← DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji, ContinuousLinearEquiv.symm_apply_apply]
    exact hj

end

end OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateHigherElimination.Dolbeault
