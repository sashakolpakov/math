import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleOrthogonality
import OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CyclePushPairing
import OAI.AlgebraicGeometry.ComplexMultiplication.CMKnownResults

/-! # Cycle Classes -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleClasses.CM.Abelian

noncomputable section

/-! Algebraic cycle classes have diagonal Hodge type, derived by resolution and duality. -/

theorem irreducible_cycleClass_isHodge
    (hBlowups : CycleResolution.CM.Abelian.ResolutionInput) (hFunctoriality : CycleResolution.CM.Abelian.ResolutionClassInput) (hHodgeDecomposition : Decomposition.CM.Abelian.HodgeDecompositionInput)
    {X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : CycleClass.Geometric.DimensionCycles.DimensionCycleSupport X p) :
    Z.geometricCycleClass ∈ X.rationalHodgeClasses p := by
  have hp : p ≤ X.complexDimension := by
    rw [X.complexDimension_eq_transcendenceDimension]
    exact Z.codimension_le_ambient
  let q := X.complexDimension - p
  have hdim : (p + p) + (q + q) = 2 * X.complexDimension := by dsimp [q]; omega
  change X.rationalCohomologyInclusion (p + p) Z.geometricCycleClass ∈ X.pureBettiSubspace p p
  apply Pairing.CM.Abelian.mem_diagonal_of_annihilates_offDiagonal
    (ProjectivePairing.CM.Abelian.projectiveComplexPairing X (p + p) (q + q) hdim)
    (X.pureBettiSubspace p p) (Decomposition.CM.Abelian.offDiagonalBettiSubspace X p)
    (X.pureBettiSubspace q q) (Decomposition.CM.Abelian.offDiagonalBettiSubspace X q)
    (Decomposition.CM.Abelian.diagonal_sup_offDiagonal hHodgeDecomposition X p) (Decomposition.CM.Abelian.diagonal_sup_offDiagonal hHodgeDecomposition X q)
    (ProjectivePairing.CM.Abelian.projectiveComplexPairing_left_nondegenerate X (p + p) (q + q) hdim)
    (CycleOrthogonality.CM.Abelian.projectivePairing_diagonal_offDiagonal X p q hdim)
    (CycleOrthogonality.CM.Abelian.projectivePairing_offDiagonal_diagonal X p q hdim)
  intro b hb
  obtain ⟨R, g, hg, hres, hdeg⟩ := CycleResolution.CM.Abelian.cycleSupport_has_resolution hBlowups Z
  have hR : (0 + 0) + (q + q) = 2 * R.complexDimension := by omega
  rw [hFunctoriality Z g hg hres hdeg,
    CyclePushPairing.CM.Abelian.projectivePairing_cohomologyPushforward g hg 0 p (q + q) hdeg (Nat.zero_le _) hR hdim]
  rw [CycleOrthogonality.CM.Abelian.pullback_offDiagonal_top_eq_zero g q (by omega) b hb]
  exact LinearMap.congr_fun
    (map_zero (ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (TopCat.of R.analyticSpace) (q + q))) _

/-- Rational linear combinations of actual algebraic supports remain of Hodge type. -/
theorem cycleClassesAreHodge_of_geometric_inputs
    (hBlowups : CycleResolution.CM.Abelian.ResolutionInput) (hFunctoriality : CycleResolution.CM.Abelian.ResolutionClassInput) (hHodgeDecomposition : Decomposition.CM.Abelian.HodgeDecompositionInput) :
    ComplexMultiplication.CMKnownResults.CM.KnownResults.CycleClassesAreHodge := by
  intro X p a ha
  obtain ⟨z, rfl⟩ := ha
  classical
  rw [CycleClass.Geometric.DimensionCycles.DimensionCycle.eq_sum_support z, map_sum]
  apply (X.rationalHodgeClasses p).sum_mem
  intro Z _
  rw [map_smul, Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.geometricCycleClassMap_single, one_smul]
  exact (X.rationalHodgeClasses p).smul_mem (z Z)
    (irreducible_cycleClass_isHodge hBlowups hFunctoriality hHodgeDecomposition Z)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMVariety.CycleClasses.CM.Abelian
