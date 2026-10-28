import OAI.AlgebraicGeometry.ComplexMultiplication.ConcreteOneCovectorSplit
import OAI.AlgebraicGeometry.ComplexMultiplication.Reference.Canonical
import OAI.AlgebraicGeometry.ComplexMultiplication.BareComparison
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport

/-! # Canonical Abelian Weight One -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalAbelianWeightOne

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry ComplexPoint
open scoped TensorProduct

attribute [-instance] ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.instTopologicalSpace

variable (X : Over (Spec (.of ℂ))) [IsIntegral X.left] [Smooth X.hom]
  [Foundations.ProjectiveSpaceIs.IsProjective X.hom]

local notation "V" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalIntegralProjectiveVariety X
local notation "A" => OAI.AlgebraicGeometry.ComplexMultiplication.BundledAbelianBridge.originalAbelianVariety X

set_option backward.isDefEq.respectTransparency false in
/-- The actual rational Betti H¹ is finite through the original geometric comparison. -/
theorem originalNativeH1_finite : FiniteDimensional ℚ ((V).rationalCohomology 1) := by
  let := BareComparison.rationalCohomology_finite X 1
  let e := Reference.BettiBridge.schemeConstantCohomologyBridgeEquiv ℚ X 1
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

set_option backward.isDefEq.respectTransparency false in
/-- The actual coefficient extension, with its proved inverse. -/
def originalNativeH1ComplexificationEquiv :
    WeightOne.CM.Complexification ((V).rationalCohomology 1) ≃ₗ[ℂ] (V).complexCohomology 1 := by
  let : FiniteDimensional ℚ
      (AlgebraicTopology.Cohomology.Singular.Basic.singularCohomology (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X) 1) :=
    originalNativeH1_finite X
  exact CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace X) 1

variable [GrpObj X]

set_option backward.isDefEq.respectTransparency false in
/-- The prescribed pure Betti pieces have zero intersection by actual invariant covectors. -/
theorem originalNativeH1_pure_disjoint :
    Disjoint ((V).pureBettiSubspace 1 0) ((V).pureBettiSubspace 0 1) := by
  let e := AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1
  apply Submodule.disjoint_def.mpr
  intro z hz kz
  have h10 : e.symm z ∈ Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (V).analyticModel 1 0 := by
    apply (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 1 0 (e.symm z)).mp
    change e (e.symm z) ∈ (V).pureBettiSubspace 1 0
    exact (e.apply_symm_apply z).symm ▸ hz
  have h01 : e.symm z ∈ Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (V).analyticModel 0 1 := by
    apply (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 0 1 (e.symm z)).mp
    change e (e.symm z) ∈ (V).pureBettiSubspace 0 1
    exact (e.apply_symm_apply z).symm ▸ kz
  apply e.symm.injective
  exact (Submodule.disjoint_def.mp (ConcreteOneCovectorSplit.oneCovector_pure_disjoint (V).analyticModel) _ h10 h01).trans
    e.symm.map_zero.symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual holomorphic and antiholomorphic invariant covectors span actual Betti H¹. -/
theorem originalNativeH1_pure_sup_top :
    (V).pureBettiSubspace 1 0 ⊔ (V).pureBettiSubspace 0 1 = ⊤ := by
  let e := AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv A 1
  apply top_unique
  intro z _
  have hz : e.symm z ∈ Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (V).analyticModel 1 0 ⊔
      Analysis.DifferentialForms.Manifold.Bidegree.pureBidegreeSubmodule (V).analyticModel 0 1 := by
    rw [ConcreteOneCovectorSplit.oneCovector_pure_sup_top]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hz
  apply Submodule.mem_sup.mpr
  refine ⟨e a, (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 1 0 a).mpr ha,
    e b, (AbelianVariety.PureAverage.Constructions.ExteriorCohomology.abelianModelCovectorBettiEquiv_pure A 0 1 b).mpr hb, ?_⟩
  exact (e.map_add a b).symm.trans ((congrArg e hab).trans (e.apply_symm_apply z))

omit [GrpObj X] in
set_option backward.isDefEq.respectTransparency false in
/-- Coefficient conjugation retains genuine singular-cochain conjugation. -/
theorem originalNativeH1_complexification_conjugation
    (x : WeightOne.CM.Complexification ((V).rationalCohomology 1)) :
    CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1
      (WeightOne.CM.coefficientConjugation ((V).rationalCohomology 1) x) =
    HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V
      (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1 x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
    rw [WeightOne.CM.coefficientConjugation_tmul, CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
      CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    exact (((HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V).map_smulₛₗ z
      (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X) 1 c)).trans
        (congrArg (fun y : (V).complexCohomology 1 => star z • y)
          (HodgeComparison.PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace X) c))).symm
  | add x y hx hy => simp only [map_add, hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- The original abelian variety has the canonical Hodge structure, with no existence premise. -/
def originalCanonicalH1 : WeightOne.CM.WeightOneHodgeStructure ((V).rationalCohomology 1) where
  finiteDimensional := originalNativeH1_finite X
  holomorphic := ((V).pureBettiSubspace 1 0).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1)
  antiholomorphic := ((V).pureBettiSubspace 0 1).comap
    (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1)
  complementary := by
    let e := originalNativeH1ComplexificationEquiv X
    exact (Submodule.orderIsoMapComap e).symm.isCompl
      ⟨originalNativeH1_pure_disjoint X, codisjoint_iff.mpr (originalNativeH1_pure_sup_top X)⟩
  conjugate_mem := by
    intro x
    constructor
    · intro hx
      have h := HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic V _ hx
      have hc := originalNativeH1_complexification_conjugation X
        (WeightOne.CM.coefficientConjugation ((V).rationalCohomology 1) x)
      have hi := congrArg (CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1)
        (WeightOne.CM.coefficientConjugation_involutive ((V).rationalCohomology 1) x)
      change CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1 x ∈
        (V).pureBettiSubspace 1 0
      exact (hc.symm.trans hi) ▸ h
    · intro hx
      change CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X) 1
        (WeightOne.CM.coefficientConjugation ((V).rationalCohomology 1) x) ∈ (V).pureBettiSubspace 0 1
      exact (originalNativeH1_complexification_conjugation X x).symm ▸
        HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_holomorphic V _ hx

/-- Its prescribed Hodge subspaces are literally the actual canonical Betti pieces. -/
theorem originalCanonicalH1_isCanonical :
    HodgeConjecture.DegreeTwo.Transport.Constructions.IsCanonicalH1 (A).variety (originalCanonicalH1 X) := ⟨rfl, rfl⟩

end

end OAI.AlgebraicGeometry.ComplexMultiplication.CanonicalAbelianWeightOne
