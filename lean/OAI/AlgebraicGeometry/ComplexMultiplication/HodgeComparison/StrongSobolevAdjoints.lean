import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevOperators
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Strong Sobolev Adjoints -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevAdjoints.CM.Construction

noncomputable section

/-! Constant postcomposition and its Hilbert adjoint preserve all orders of
actual L2 derivatives, through their spatial difference commutation. -/

open _root_.MeasureTheory

variable {E F G ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [Fintype ι]

omit [Fintype ι] in
theorem realL2Difference_compLpL (T : F →L[ℝ] G) (m : E) (t : ℝ)
    (u : Lp F 2 (volume : Measure E)) :
    DifferenceProduct.CM.Construction.realL2Difference m t (T.compLpL 2 volume u) = T.compLpL 2 volume (DifferenceProduct.CM.Construction.realL2Difference m t u) := by
  apply Lp.ext
  filter_upwards [DifferenceProduct.CM.Construction.realL2Difference_coe m t (T.compLpL 2 volume u), T.coeFn_compLpL u,
    (measurePreserving_add_right volume (t • m)).quasiMeasurePreserving.ae (T.coeFn_compLpL u),
    T.coeFn_compLpL (DifferenceProduct.CM.Construction.realL2Difference m t u), DifferenceProduct.CM.Construction.realL2Difference_coe m t u]
    with x hd h0 ht hT hdu
  rw [hd, h0, ht, hT, hdu, map_smul, map_sub]

theorem strongSobolev_compLpL (b : OrthonormalBasis ι ℝ E) (T : F →L[ℝ] G) (n : ℕ)
    {u : Lp F 2 (volume : Measure E)} (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (T.compLpL 2 volume u) :=
  hu.map b (T.compLpL 2 volume) (fun i t u => realL2Difference_compLpL T (b i) t u) n

variable [CompleteSpace F] [CompleteSpace G]

theorem realL2Difference_adjoint_comm (b : OrthonormalBasis ι ℝ E)
    (T : Lp F 2 (volume : Measure E) →L[ℝ] Lp G 2 (volume : Measure E))
    (hT : ∀ i : ι, ∀ t : ℝ, ∀ u : Lp F 2 (volume : Measure E),
      DifferenceProduct.CM.Construction.realL2Difference (b i) t (T u) = T (DifferenceProduct.CM.Construction.realL2Difference (b i) t u))
    (i : ι) (t : ℝ) (u : Lp G 2 (volume : Measure E)) :
    DifferenceProduct.CM.Construction.realL2Difference (b i) t (T.adjoint u) = T.adjoint (DifferenceProduct.CM.Construction.realL2Difference (b i) t u) := by
  apply ext_inner_right ℝ
  intro v
  calc
    _ = -inner ℝ (T.adjoint u) (DifferenceProduct.CM.Construction.realL2Difference (b i) (-t) v) := DifferenceProduct.CM.Construction.realL2Difference_inner _ _ _ _
    _ = -inner ℝ u (T (DifferenceProduct.CM.Construction.realL2Difference (b i) (-t) v)) := by rw [ContinuousLinearMap.adjoint_inner_left]
    _ = -inner ℝ u (DifferenceProduct.CM.Construction.realL2Difference (b i) (-t) (T v)) := by rw [hT]
    _ = inner ℝ (DifferenceProduct.CM.Construction.realL2Difference (b i) t u) (T v) := (DifferenceProduct.CM.Construction.realL2Difference_inner _ _ _ _).symm
    _ = _ := (T.adjoint_inner_left v (DifferenceProduct.CM.Construction.realL2Difference (b i) t u)).symm

theorem strongSobolev_adjoint_of_difference_comm (b : OrthonormalBasis ι ℝ E)
    (T : Lp F 2 (volume : Measure E) →L[ℝ] Lp G 2 (volume : Measure E))
    (hT : ∀ i : ι, ∀ t : ℝ, ∀ u : Lp F 2 (volume : Measure E),
      DifferenceProduct.CM.Construction.realL2Difference (b i) t (T u) = T (DifferenceProduct.CM.Construction.realL2Difference (b i) t u))
    (n : ℕ) {u : Lp G 2 (volume : Measure E)} (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n (T.adjoint u) :=
  hu.map b T.adjoint (realL2Difference_adjoint_comm b T hT) n

theorem strongSobolev_compLpL_adjoint (b : OrthonormalBasis ι ℝ E) (T : F →L[ℝ] G) (n : ℕ)
    {u : Lp G 2 (volume : Measure E)} (hu : StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n u) :
    StrongSobolev.CM.Construction.HasStrongSobolevDerivatives b n ((T.compLpL 2 volume).adjoint u) :=
  strongSobolev_adjoint_of_difference_comm b (T.compLpL 2 volume)
    (fun i t u => realL2Difference_compLpL T (b i) t u) n hu

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.StrongSobolevAdjoints.CM.Construction
