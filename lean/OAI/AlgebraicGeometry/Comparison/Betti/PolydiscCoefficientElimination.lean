import OAI.AlgebraicGeometry.Comparison.Betti.HigherFormCoefficientElimination
import OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionTransport

/-! # Polydisc Coefficient Elimination -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PolydiscCoefficientElimination.Dolbeault

noncomputable section

/-! Eliminate any selected antiholomorphic coordinate of an actual
higher-degree closed pure form on a finite polydisc. -/

open _root_.TopologicalSpace

theorem correctOpenDolbeaultForm_add_dbar {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]
    {U : Opens E} (n : ℕ) (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U (n + 1)) (u : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm U n) :
    Open.DolbeaultCorrection.correctOpenDolbeaultForm n a u + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u = a := by
  ext x v
  change (a x v - DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u x v) + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD n u x v = a x v
  ring

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_polydisc_higherForm_coefficient_elimination (U : ι → Opens ℂ)
    (n p q : ℕ) (hn : n + 1 = p + q)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (n + 2)) (ha : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) a = 0)
    (hpure : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) a) (x : DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (i : ι) :
    ∃ W : Opens ℂ, x.val i ∈ W ∧ ∃ hW : W ≤ U i,
      ∃ b : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) (n + 2),
      ∃ t : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (Function.update U i W)) (n + 1),
        b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t = Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (DivisorClass.Chern.CoordinatePolydiscUpdate.coordinatePolydisc_update_le U i W hW) a ∧
          DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) b = 0 ∧ DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) b ∧
          DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p q t ∧
          Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) b = 0 ∧
          (∀ j : ι, j ≠ i → Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) a = 0 →
            Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ (n + 1) (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) b = 0) := by
  let S := DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)
  let A : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (ContractionCauchyPrimitive.Dolbeault.productOpen S (U i)) (n + 2) := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormToProduct U i a
  have hA : DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 2) A = 0 := DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_closed
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) a ha
  have hAp : DivisorClass.Chern.Open.DolbeaultPrime.OpenFormHasBidegree p (q + 1) A := DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree
    (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm.toContinuousLinearMap (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate_symm_mapsTo U i) hpure
  obtain ⟨W, hxW, hW, u, hup, hB, hBp, hBzero, hBprior⟩ :=
    HigherFormCoefficientElimination.Dolbeault.exists_higherForm_coefficient_elimination n p q hn A hA hAp
      ((DivisorClass.Chern.Complex.CoordinateSplit.mem_coordinatePolydisc U x).mp x.property i)
  let B := Open.DolbeaultCorrection.correctOpenDolbeaultForm (n + 1) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (HigherFormCoefficientElimination.Dolbeault.productOpen_mono hW) A) u
  let b := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct U i W B
  let t := DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct U i W u
  have hsum : b + DivisorClass.Chern.DolbeaultOpen.openDolbeaultD (n + 1) t =
      Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (DivisorClass.Chern.CoordinatePolydiscUpdate.coordinatePolydisc_update_le U i W hW) a := by
    have hs := congrArg (DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct U i W)
      (correctOpenDolbeaultForm_add_dbar (n + 1) (Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm.restrict (HigherFormCoefficientElimination.Dolbeault.productOpen_mono hW) A) u)
    erw [(DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct U i W).map_add, DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct_d] at hs
    dsimp only [A] at hs
    erw [DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct_restrict_inverse U i W hW a] at hs
    exact hs
  refine ⟨W, hxW, hW, b, t, hsum,
    DivisorClass.Chern.CoordinatePullbackIdentities.complexLinearOpenPullback_closed (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (DivisorClass.Chern.CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) B hB,
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (DivisorClass.Chern.CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) hBp,
    DivisorClass.Chern.Complex.LinearOpenPullback.complexLinearOpenPullback_hasBidegree (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).toContinuousLinearMap
      (DivisorClass.Chern.CoordinatePolydiscUpdate.splitComplexCoordinate_update_mapsTo U i W) hup,
    Coordinate.ContractionTransport.Dolbeault.coordinateFormFromProduct_contraction_same_zero (n + 1) U i W B hBzero, ?_⟩
  intro j hji hj
  apply Coordinate.ContractionTransport.Dolbeault.coordinateFormFromProduct_contraction_other_zero (n + 1) U i j hji W B
  exact hBprior (fun k : {k : ι // k ≠ i} => DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j k)
    (Coordinate.ContractionTransport.Dolbeault.coordinateFormToProduct_contraction_other_zero (n + 1) U i j hji a hj)

end

end OAI.AlgebraicGeometry.Comparison.Betti.PolydiscCoefficientElimination.Dolbeault
