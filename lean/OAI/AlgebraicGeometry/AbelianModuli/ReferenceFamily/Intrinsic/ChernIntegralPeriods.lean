import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChernEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.LoopTrianglePairing
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernPairing

/-! # Chern Integral Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods

noncomputable section

/-! The original algebraic Chern form takes integer values on the
original native period lattice. No multiple of the line bundle or form is used. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

theorem nativeChernForm_integral (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
    (ℓ μ : HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) :
    ∃ k : ℤ, (k : ℚ) = ChernPairing.nativeChernForm A L
      (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ℓ)
      (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) μ) := by
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.stronglyLocallyContractibleSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  let := AlgebraicTopology.Cohomology.Singular.ChartLocalContractible.locallyPathConnectedSpace_of_chartedSpace A.variety.analyticModel A.variety.analyticSpace
  obtain ⟨k, hk⟩ := Integral.ChernEvaluation.nativeChernClass_evaluation_is_integer A.variety.presentation L
    (IntegralLoopTriangles.nativeIntegralLoopTriangleClass A ℓ μ)
  refine ⟨k, hk.trans ?_⟩
  change LoopTrianglePairing.nativeLoopTriangleEvaluation A ℓ μ (ChernClasses.lineBundleChernClass A.variety.presentation L) = _
  rw [LoopTrianglePairing.nativeLoopTriangleEvaluation_eq_original]
  have hm : ChernPairing.nativeMultiplication A = AbelianVariety.DoublingDifference.Constructions.ExteriorCohomology.abelianMulTop A := by
    apply TopCat.ext
    intro x
    rfl
  change HomologyCrossPairing.homologyClassPairing _ _ _ _ _ = HomologyCrossPairing.alternatingClassPairing _ (ChernPairing.nativeMultiplication A) _ _ _
  rw [hm, HomologyPairingAntisymmetry.alternatingClassPairing_eq_original]
  rfl

def nativeIntegralChernMatrix {ι : Type} (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (b : Module.Basis ι ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) : Matrix ι ι ℤ :=
  fun i j => (nativeChernForm_integral A L (b i) (b j)).choose

theorem nativeIntegralChernMatrix_cast {ι : Type} (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (b : Module.Basis ι ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) (i j : ι) :
    (nativeIntegralChernMatrix A L b i j : ℚ) = ChernPairing.nativeChernForm A L
      (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b i))
      (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b j)) :=
  (nativeChernForm_integral A L (b i) (b j)).choose_spec

private theorem nativeIntegralChern_skew {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (hH : ∀ x, H x x = 0) (x y : V) :
    H y x = -H x y := by
  have h := hH (x + y)
  simp only [map_add, LinearMap.add_apply, hH, zero_add, add_zero] at h
  linarith only [h]

theorem nativeIntegralChernMatrix_alternating {ι : Type} (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left) (b : Module.Basis ι ℤ (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A)) :
    (nativeIntegralChernMatrix A L b).transpose = -nativeIntegralChernMatrix A L b := by
  ext i j
  apply Int.cast_injective (α := ℚ)
  change (nativeIntegralChernMatrix A L b j i : ℚ) = (-nativeIntegralChernMatrix A L b i j : ℤ)
  rw [Int.cast_neg, nativeIntegralChernMatrix_cast, nativeIntegralChernMatrix_cast]
  exact nativeIntegralChern_skew (ChernPairing.nativeChernForm A L) (ChernPairing.nativeChernForm_alternating A L)
    (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b i))
    (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b j))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ChernIntegralPeriods
