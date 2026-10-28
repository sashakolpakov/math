import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CupScalarExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.KnownRealization
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PolarizationFactor

/-! # Geometric Pairing -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.GeometricPairing.CM.Construction

noncomputable section

/-!
The geometric middle pairing for CMReduction: cup two realized H¹ classes with
the rational Fubini--Study class to the power dim(B)-1. A polarization
factoring through this actual cup pairing is constructed in the conclusion.
-/

open scoped TensorProduct

open OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CupScalarExtension.CM.Construction

variable {U : Type} [AddCommGroup U] [Module ℚ U]
  {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)

def realizedTopCup (k : ℕ) : U →ₗ[ℚ] U →ₗ[ℚ]
    R.abelianVariety.variety.rationalCohomology (2 + (k + k)) :=
  (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.rationalH1TopCup R.abelianVariety.variety k).compl₁₂
    R.comparison.toLinearMap R.comparison.toLinearMap

theorem realizedTopCup_comparison (k : ℕ) (u v : ComplexMultiplication.WeightOne.CM.Complexification U) :
    ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup R.abelianVariety.variety k (R.complexComparison u) (R.complexComparison v) =
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
        (2 + (k + k)) (LinearMap.BilinMap.baseChange ℂ (realizedTopCup R k) u v) := by
  apply ComplexMultiplication.HodgeComparison.BilinearRational.CM.Construction.bilinearScalarExtension_comparison (realizedTopCup R k)
    (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup R.abelianVariety.variety k) R.complexComparison.toLinearMap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace R.abelianVariety.toOver)
      (2 + (k + k))) ?_ u v
  intro x y
  simp only [ComplexMultiplication.CMKnownResults.CM.HodgeRealization.complexComparison_apply, LinearEquiv.coe_coe,
    LinearMap.baseChange_tmul, ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1ScalarExtension_tmul,
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
  exact (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.rationalH1TopCup_comparison R.abelianVariety.variety k
    (R.comparison x) (R.comparison y)).symm

theorem canonical_h1_conjugation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) =
    ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
      rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      exact (((ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V).map_smulₛₗ z
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace V.toOver) 1 c)).trans
          (congrArg (fun y : V.complexCohomology 1 => star z • y)
            (ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace V.toOver) c))).symm
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realized_comparison_conjugation (u : ComplexMultiplication.WeightOne.CM.Complexification U) :
    R.complexComparison (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) =
      ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 R.abelianVariety.variety (R.complexComparison u) := by
  rw [ComplexMultiplication.CMKnownResults.CM.HodgeRealization.complexComparison_apply, ComplexMultiplication.CMKnownResults.CM.HodgeRealization.complexComparison_apply,
    ComplexMultiplication.WeightOne.CM.baseChange_coefficientConjugation]
  exact canonical_h1_conjugation R.abelianVariety.variety _

/-- The required geometric identification is constructed, with no assumed
equality between an arbitrary polarization and a geometric cup pairing. -/
theorem exists_realizedTopCup_polarization (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ R.abelianVariety.variety.analyticModel) :
    ∃ (P : ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
      (trace : R.abelianVariety.variety.rationalCohomology (2 + (k + k)) →ₗ[ℚ] ℚ),
      P.form = (realizedTopCup R k).compr₂ trace := by
  let V := R.abelianVariety.variety
  let : FiniteDimensional ℚ (V.rationalCohomology (2 + (k + k))) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite V _
  let j := ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))
  let T := (ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace V k).comp j
  apply PolarizationFactor.CM.Construction.exists_polarization_factoring H (realizedTopCup R k) ?_ ?_ T ?_ ?_
  · intro u
    exact ComplexMultiplication.HodgeComparison.TopAlternating.CM.Construction.rationalH1TopCup_self V k (R.comparison u)
  · intro u hu v hv
    apply ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))
    rw [map_zero, ← realizedTopCup_comparison]
    exact ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup_holomorphic_zero V k hdim _ _
      ((R.complexComparison_holomorphic u).mpr hu)
      ((R.complexComparison_holomorphic v).mpr hv)
  · intro w
    change (ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace V k (j ((1 : ℂ) ⊗ₜ[ℚ] w))).im = 0
    rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
    exact ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace_rational_real V k w
  · intro u hu hne
    change 0 < (Complex.I * ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace V k
      (j (LinearMap.BilinMap.baseChange ℂ (realizedTopCup R k) u
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation U u)))).re
    rw [← realizedTopCup_comparison, realized_comparison_conjugation]
    apply ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace_holomorphic_positive V k hdim _
      ((R.complexComparison_holomorphic u).mpr hu)
    exact (R.complexComparison.map_ne_zero_iff).mpr hne

/-- Opposite embedding lines pair nontrivially by actual cup product
against the geometric ample power, as required by the manuscript. -/
theorem geometric_opposite_pairing_ne_zero
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [Module E U] [IsScalarTower ℚ E U]
    (h_PolarizedPairing : Pairing.CM.Construction.PolarizedPairingInput) (hCM : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (k : ℕ) (hdim : k + 1 = Module.finrank ℂ R.abelianVariety.variety.analyticModel)
    (σ : E →ₐ[ℚ] ℂ) (u v : ComplexMultiplication.WeightOne.CM.Complexification U)
    (hu : u ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ)
    (hv : v ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ))
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup R.abelianVariety.variety k (R.complexComparison u) (R.complexComparison v) ≠ 0 := by
  obtain ⟨P, trace, hP⟩ := exists_realizedTopCup_polarization R k hdim
  have hn := PolarizationFactor.CM.Construction.vector_pairing_ne_zero_of_polarization h_PolarizedPairing H P hCM
    (realizedTopCup R k) trace hP σ u v hu hv hu0 hv0
  intro hz
  apply hn
  let : FiniteDimensional ℚ (R.abelianVariety.variety.rationalCohomology (2 + (k + k))) :=
    AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite R.abelianVariety.variety _
  apply ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_injective
    (Betti.Scheme.schemePointSpace R.abelianVariety.toOver) (2 + (k + k))
  rw [map_zero, ← realizedTopCup_comparison, hz]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.GeometricPairing.CM.Construction
