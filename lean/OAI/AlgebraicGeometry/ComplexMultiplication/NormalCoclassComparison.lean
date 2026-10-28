import OAI.AlgebraicGeometry.ComplexMultiplication.RelativeDualAbsoluteExtension
import OAI.AlgebraicGeometry.CycleClass.Geometric.RationalLocalPurity
import OAI.AlgebraicTopology.LocalHomology.NormalProjectionCoclass

/-! # Normal Coclass Comparison -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.NormalCoclassComparison

noncomputable section

/-! # The two actual rational normal coclasses span the same line

The original explicit complex orientation and the native integral homology
normalization both give nonzero classes in the genuine one-dimensional local
cohomology group. Their comparison is a nonzero rational scalar depending only
on the codimension. This suffices for the rational cycle-class span.
-/

open _root_.CategoryTheory OAI.AlgebraicTopology.Singular

/-- The unchanged original class, normalized against its explicit complex orientation. -/
def originalNormalCoclass (p : ℕ) : AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p) (2 * p) :=
  Cycle.LocalPurity.AlgebraicTopology.Singular.normalizedRelativeCoclass (AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ p)
    (AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_for_chart p)

/-- The original normal coclass is nonzero, by its actual evaluation pairing. -/
theorem originalNormalCoclass_ne_zero (p : ℕ) : originalNormalCoclass p ≠ 0 := by
  intro h
  have hn := Cycle.LocalPurityOf.AlgebraicTopology.Singular.normalizedRelativeCoclass_pairing_self
    (AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ p) (AlgebraicTopology.LocalHomology.ChartFundamentalClassGenerator.Singular.standardComplexLocalClass_ne_zero_for_chart p)
  change AlgebraicTopology.Singular.Cohomology.relativeCohomologyEquivDualHomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p) (2 * p)
    (originalNormalCoclass p) (AlgebraicTopology.LocalHomology.ComplexClass.Singular.standardComplexLocalClass ℚ p) = 1 at hn
  rw [h, map_zero, LinearMap.zero_apply] at hn
  exact zero_ne_one hn

/-- The genuine normal cohomology comparison between the two chain constructions. -/
def normalCohomologyBridge (p : ℕ) :
    CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalLocalCohomology p (2 * p) ≃ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology.RelativeCohomology ℚ (AlgebraicTopology.LocalHomology.FundamentalClass.Singular.puncturedPair ℂ p) (2 * p) :=
  RelativeSingularCochainBridge.relativeSingularCohomologyBridgeEquiv ℚ (TopCat.of (Fin p → ℂ)) {0}ᶜ (2 * p)

/-- The coefficient is read from the actual original class in the actual native normal group. -/
def normalCoclassCoefficient (p : ℕ) : ℚ :=
  CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv p
    ((normalCohomologyBridge p).symm (originalNormalCoclass p))

/-- The two specified normal coclasses differ by this actual rational coefficient. -/
theorem normalCoclassCoefficient_smul (p : ℕ) :
    normalCohomologyBridge p
        (normalCoclassCoefficient p • CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass p) =
      originalNormalCoclass p := by
  apply (normalCohomologyBridge p).symm.injective
  simp only [LinearEquiv.symm_apply_apply]
  apply (CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalTopCohomologyEquiv p).injective
  simp only [map_smul, CycleClass.Geometric.RationalLocalPurity.Cycles.complexNormalRationalDualClass_normalization,
    smul_eq_mul, mul_one, normalCoclassCoefficient]

/-- Neither actual normalization can annihilate the normal orientation line. -/
theorem normalCoclassCoefficient_ne_zero (p : ℕ) : normalCoclassCoefficient p ≠ 0 := by
  intro h
  have hn := normalCoclassCoefficient_smul p
  rw [h, zero_smul, map_zero] at hn
  exact originalNormalCoclass_ne_zero p hn.symm

end

end OAI.AlgebraicGeometry.ComplexMultiplication.NormalCoclassComparison
