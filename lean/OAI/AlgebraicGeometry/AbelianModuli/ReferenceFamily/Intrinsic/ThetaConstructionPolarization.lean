import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Integral.ChernMatrixNondegenerate
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Prerequisite
import OAI.AlgebraicGeometry.Picard.ThetaConstruction.IntrinsicPolarization

/-! # Theta Construction Polarization -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ThetaConstructionPolarization

noncomputable section

/-! Construct ThetaConstruction's exact integral polarization matrix from the original
ample algebraic line bundle. The period, lattice, and Riemann-form
comparisons are proved rather than supplied as additional hypotheses. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {g : ℕ} (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (L : HilbertConstruction.Line.Bundles.LineBundle A.toOver.left)
  (hL : L.IsAmple) (b : ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.Marking (Picard.ThetaConstruction.DefinitionsIntegral.Index g) A)

theorem nativeIntegralChernMatrix_preserves :
    Picard.ThetaConstruction.IntrinsicPolarization.Geometric.PreservesPolarizationMatrix A L hL b (ChernIntegralPeriods.nativeIntegralChernMatrix A L b) := by
  intro i j
  have h := RiemannForm.nativeRiemannForm_period A L hL
    (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b i))
    (LatticePeriodEvaluation.LatticeCharacters.latticeInclusion (HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) (b j))
  refine h.trans ?_
  simpa using congrArg (fun q : ℚ => (q : ℝ)) (ChernIntegralPeriods.nativeIntegralChernMatrix_cast A L b i j).symm

theorem nativeIntegralChernMatrix_eq_of_preserves (J : Picard.ThetaConstruction.DefinitionsIntegral.IntegralMatrix g)
    (hJ : Picard.ThetaConstruction.IntrinsicPolarization.Geometric.PreservesPolarizationMatrix A L hL b J) :
    ChernIntegralPeriods.nativeIntegralChernMatrix A L b = J := by
  ext i j
  apply Int.cast_injective (α := ℝ)
  exact (nativeIntegralChernMatrix_preserves A L hL b i j).symm.trans (hJ i j)

theorem nativeThetaConstruction_polarized_comparison :
    ∃ (T : Picard.ThetaConstruction.DefinitionsIntegral.MarkedPolarizedTorus g (ChernIntegralPeriods.nativeIntegralChernMatrix A L b))
      (e : HodgeConjecture.DegreeTwo.Transport.Constructions.AbelianModel A ≃ₗ[ℂ] Picard.ThetaConstruction.DefinitionsIntegral.Tangent g),
      (∀ z, T.periodMap z = e (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b z)) ∧
      (∀ v, v ∈ T.lattice ↔ e.symm v ∈ HodgeConjecture.DegreeTwo.AbelianUniformizationEq.Constructions.AbelianUniformization.periodLattice A) ∧
      (∀ u v, T.riemannForm (e u) (e v) = RiemannForm.nativeRiemannForm A L hL u v) ∧
      T.periodMap.ker = (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker := by
  obtain ⟨T, e, hp, hl, hH⟩ := Picard.ThetaConstruction.IntrinsicPolarization.Geometric.native_polarized_comparison
    A L hL b (ChernIntegralPeriods.nativeIntegralChernMatrix A L b) (nativeIntegralChernMatrix_preserves A L hL b)
  refine ⟨T, e, hp, hl, hH, ?_⟩
  ext z
  simp only [LinearMap.mem_ker, hp, map_eq_zero_iff e e.injective]

include hL in
theorem nativeThetaConstruction_positive_period (hThetaConstruction : Prerequisite.ThetaConstructionFullStatement) :
    Picard.ThetaConstruction.DefinitionsIntegral.CompatiblePositivePeriod (ChernIntegralPeriods.nativeIntegralChernMatrix A L b) (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker := by
  obtain ⟨T, _, _, _, _, hk⟩ := nativeThetaConstruction_polarized_comparison A L hL b
  exact ((hThetaConstruction g (ChernIntegralPeriods.nativeIntegralChernMatrix A L b)
    (ChernIntegralPeriods.nativeIntegralChernMatrix_alternating A L b)
    (Integral.ChernMatrixNondegenerate.nativeIntegralChernMatrix_det_ne_zero A L b hL)).1 (ArithmeticGeometry.Descent.CMVariety.MarkedAbelianPeriods.IntrinsicPeriods.periodMap b).ker).mpr ⟨T, hk⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.ThetaConstructionPolarization
