import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.LineOneFormElimination
import OAI.AlgebraicGeometry.Comparison.Betti.ProductCoordinateHigherElimination
import OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis

/-! # Coordinate One Form Elimination -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.CoordinateOneFormElimination.Dolbeault

noncomputable section

section

/-! Global elimination of a selected one-form coefficient on a product
of ordinary and punctured complex coordinate lines. -/

open _root_.TopologicalSpace Set

open OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_product_coordinate_oneForm_elimination (ε : ι → Bool)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 1) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (i : ι) :
    ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 1,
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 0,
      b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 t = a ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 b ∧
        (∀ y : ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε, DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (b y) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) = 0) ∧
        (∀ j : ι, j ≠ i →
          (∀ y : ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε, DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (a y) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) = 0) →
          ∀ y : ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε, DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (b y) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) = 0) := by
  let U := fun j => PuncturedParametricDbar.Dolbeault.cauchyCoordinateOpen (ε j)
  let S := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)
  let A := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormToProduct U i a
  have hA : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 A = 0 := DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_closed
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) a ha
  have hAp : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 A := DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) hpure
  obtain ⟨g, hg, hB, hBp, hBzero, hBprior⟩ :=
    Coordinate.LineOneFormElimination.Dolbeault.exists_coordinateLine_oneForm_coefficient_elimination S (ε i) A hA hAp
  let B := DivisorClass.Chern.DolbeaultOneFormCorrection.correctDolbeaultOneForm A g hg
  let b := ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i B
  let t := ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i (DivisorClass.Chern.ScalarDolbeaultCommutation.scalarOpenZeroForm _ g hg)
  have hsum : b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 t = a := by
    have hs := congrArg (ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i) (DivisorClass.Chern.CoordinatePullbackIdentities.correctDolbeaultOneForm_add_dbar A hg)
    erw [(ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i).map_add, ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_d] at hs
    exact hs.trans (ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_inverse U i a)
  refine ⟨b, t, hsum, ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_closed U i B hB,
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_mapsTo U i) hBp, ?_, ?_⟩
  · intro y
    change DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i B y) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) = 0
    erw [ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_coefficient, DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_same]
    exact hBzero _
  · intro j hji hj y
    change DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn U i B y) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) = 0
    erw [ProductCoordinateFormReturn.Dolbeault.productCoordinateFormReturn_coefficient, DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji]
    exact hBprior _ (DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormToProduct_zero_other U i j hji a hj) _

end

/-! Global Dolbeault exactness in degree one on products of ordinary and punctured complex lines. -/

open _root_.TopologicalSpace

open OAI.AlgebraicGeometry.DivisorClass.Chern.AntiOneFormBasis

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_product_oneForm_eliminate_finset (ε : ι → Bool)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 1) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) (s : Finset ι) :
    ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 1,
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 0,
      b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 t = a ∧ DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 b ∧
        ∀ i ∈ s, ∀ y : (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε), DivisorClass.Chern.AntiOneFormCoordinates.oneFormLinear (b y) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨a, 0, ?_, ha, hpure, ?_⟩
    · rw [map_zero, add_zero]
    · intro i hi
      exact False.elim (Finset.notMem_empty i hi)
  | @insert i s hi ih =>
    obtain ⟨b, t, hsum, hb, hbp, hzero⟩ := ih
    obtain ⟨c, u, hstep, hc, hcp, hci, hcprior⟩ :=
      exists_product_coordinate_oneForm_elimination ε b hb hbp i
    refine ⟨c, t + u, ?_, hc, hcp, ?_⟩
    · calc
        c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 (t + u) = (c + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 u) + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 t := by
          rw [map_add]
          abel
        _ = b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 t := by rw [hstep]
        _ = a := hsum
    · intro j hj y
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        exact hci y
      · exact hcprior j (fun hji => hi (hji ▸ hjs)) (hzero j hjs) y

theorem exists_product_oneForm_dolbeault_primitive (ε : ι → Bool)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 1) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 1 a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree 0 1 a) :
    ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ProductCoordinateHigherElimination.Dolbeault.coordinateLineProduct ε) 0, DivisorClass.Chern.DolbeaultOpen.openDolbeaultD 0 t = a := by
  obtain ⟨b, t, hsum, _, hbp, hzero⟩ := exists_product_oneForm_eliminate_finset ε a ha hpure Finset.univ
  have hbzero := DivisorClass.Chern.AntiOneFormBasis.antiOneForm_eq_zero_of_basis_coefficients b hbp
    (fun y i => hzero i (Finset.mem_univ i) y)
  exact ⟨t, by simpa only [hbzero, zero_add] using hsum⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.CoordinateOneFormElimination.Dolbeault
