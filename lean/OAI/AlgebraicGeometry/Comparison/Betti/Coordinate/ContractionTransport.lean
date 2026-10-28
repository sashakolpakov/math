import OAI.AlgebraicGeometry.Comparison.Betti.Open.ContractionPullback
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

/-! # Contraction Transport -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionTransport.Dolbeault

noncomputable section

/-! Transport of vanishing antiholomorphic contractions through the
actual finite-coordinate splitting equivalence. -/

open _root_.TopologicalSpace

open OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem coordinateFormFromProduct_contraction_same_zero (n : ℕ)
    (U : ι → Opens ℂ) (i : ι) (W : Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen
      (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun j : {j : ι // j ≠ i} => U j)) W) (n + 1))
    (ha : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n (0, 1) a = 0) :
    Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i) (DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct U i W a) = 0 := by
  apply Open.ContractionPullback.Dolbeault.openAntiContraction_pullback_zero
  change Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector i)) a = 0
  rw [DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_same]
  exact ha

theorem coordinateFormToProduct_contraction_other_zero (n : ℕ)
    (U : ι → Opens ℂ) (i j : ι) (hji : j ≠ i)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc U) (n + 1))
    (ha : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) a = 0) :
    Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n ((fun k : {k : ι // k ≠ i} => DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j k), 0)
      (DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormToProduct U i a) = 0 := by
  apply Open.ContractionPullback.Dolbeault.openAntiContraction_pullback_zero
  change Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n ((DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i).symm
    ((fun k : {k : ι // k ≠ i} => DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j k), 0)) a = 0
  rw [← DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji, ContinuousLinearEquiv.symm_apply_apply]
  exact ha

theorem coordinateFormFromProduct_contraction_other_zero (n : ℕ)
    (U : ι → Opens ℂ) (i j : ι) (hji : j ≠ i) (W : Opens ℂ)
    (a : Analysis.DifferentialForms.Manifold.OpenD.SmoothOpenForm (DivisorClass.Chern.OneFormCauchyElimination.complexProductOpen
      (DivisorClass.Chern.Complex.CoordinateSplit.coordinatePolydisc (fun k : {k : ι // k ≠ i} => U k)) W) (n + 1))
    (ha : Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n ((fun k : {k : ι // k ≠ i} => DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j k), 0) a = 0) :
    Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j) (DivisorClass.Chern.CoordinatePolydiscDolbeaultPoincare.coordinateFormFromProduct U i W a) = 0 := by
  apply Open.ContractionPullback.Dolbeault.openAntiContraction_pullback_zero
  change Open.AntiholomorphicContraction.Dolbeault.openAntiContraction _ n (DivisorClass.Chern.Complex.CoordinateSplit.splitComplexCoordinate i (DivisorClass.Chern.AntiOneFormBasis.complexCoordinateVector j)) a = 0
  rw [DivisorClass.Chern.AntiOneFormBasis.splitComplexCoordinate_vector_other i j hji]
  exact ha

end

end OAI.AlgebraicGeometry.Comparison.Betti.Coordinate.ContractionTransport.Dolbeault
