import OAI.AlgebraicGeometry.ComplexMultiplication.CMAbelianVariety
import OAI.AlgebraicGeometry.ComplexMultiplication.WeightOne
import OAI.AlgebraicGeometry.ComplexMultiplication.CohomologyBaseChange
import OAI.AlgebraicTopology.DeRham.Comparison.Projective
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import OAI.AlgebraicTopology.Duality.Poincare.Manifold
import OAI.AlgebraicTopology.Cohomology.Singular.UniversalCoefficient
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AlgebraicPeriodMap
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicPrimitive
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMaximum
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormProjection
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Bounds
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Smooth
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.LocalMetricEquation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceCriterion
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceBounds
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SobolevSmoothDensity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Elliptic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.DifferenceConvergence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietyInteriorRegularity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ComparisonElliptic
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.EllipticRegularity
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.VarietySmoothDirichlet
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartMeasure
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalMetricCoefficient
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevGraph
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneFormFrameChange
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ChartCutoffLp
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalWeakSolver
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalSobolevFaithful
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricEnergyInvariant
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricBochnerIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GlobalEnergyLocalization
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.SmoothPoisson
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HarmonicOneForms
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricDerivative
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.InverseCoefficientCancellation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MetricCoefficientDivergence
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicMixedChartPair
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicCodifferential
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.AdjointConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ClosedOneCodifferentialParts
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.MixedTwoChartMetric
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.HolomorphicExteriorTrace
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.GeneratedInjective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMapGluing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodMap
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureDefect
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.ProjectiveCurvatureIntegration
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.TopAlternating
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerCohomologyFunctional
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RealKahlerFunctional
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalPositiveApproximation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CovectorProduct
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerProjective
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerFunctionalPositive
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.KahlerTopTrace
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PolarizationFromRationalPairing
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CupScalarExtension
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PeriodTorusProjective
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Albanese
import Mathlib.LinearAlgebra.Projection

/-! # Hodge Comparison Is -/

namespace OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs.CM.Construction

noncomputable section

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open scoped TensorProduct

/-- The pointed universal property, as in Statements/HodgeComparison.lean. -/
def IsAlbaneseMap
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) : Prop :=
  x₀ ≫ a = η[A.toOver] ∧
  ∀ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : X.toOver ⟶ B.toOver),
    x₀ ≫ f = η[B.toOver] →
      ∃! g : A.toOver ⟶ B.toOver,
        IsMonHom g ∧ a ≫ g = f

/-- The geometric Hodge pieces, as in Statements/HodgeComparison.lean. -/
def IsCanonicalH1
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1)) : Prop :=
  H.holomorphic =
      (V.pureBettiSubspace 1 0).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
          (Betti.Scheme.schemePointSpace V.toOver) 1) ∧
  H.antiholomorphic =
      (V.pureBettiSubspace 0 1).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
          (Betti.Scheme.schemePointSpace V.toOver) 1)

/-- The stated Albanese universal property forces generation of its abelian target. -/
theorem albanese_generates (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : IsAlbaneseMap X x₀ A a) :
    Construction.GeneratedClosed.Generates X.presentation A a := by
  have h : PELModuli.IntegralModel.Albanese.IsAlbaneseMap X.presentation x₀ A a := by
    simpa only [IsAlbaneseMap, PELModuli.IntegralModel.Albanese.IsAlbaneseMap, MonObj.one_eq_one] using ha
  exact PELModuli.IntegralModel.Albanese.albanese_generates X.presentation x₀ A a h

/-- Pullback by the actual Albanese map has no kernel on rational H¹. -/
theorem albanese_h1_pullback_injective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : IsAlbaneseMap X x₀ A a) :
    Function.Injective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom :=
  ComplexMultiplication.HodgeComparison.GeneratedInjective.CM.Construction.generated_rationalBetti_h1_injective X x₀ A a (albanese_generates X x₀ A a ha)

/-- An infinite-dimensional vector space has strictly smaller dimension than
its algebraic dual, so it cannot be isomorphic to its algebraic double dual. -/
theorem finiteDimensional_of_doubleDualEquiv
    (U : Type) [AddCommGroup U] [Module ℚ U]
    (e : U ≃ₗ[ℚ] Module.Dual ℚ (Module.Dual ℚ U)) :
    FiniteDimensional ℚ U := by
  rw [FiniteDimensional, ← Module.rank_lt_aleph0_iff]
  by_contra! h
  have h₁ := rank_lt_rank_dual h
  have h₂ := rank_lt_rank_dual (h.trans h₁.le)
  exact (lt_trans h₁ h₂).ne e.rank_eq

/-- Poincare duality and field UCT identify complementary ordinary Betti
groups as algebraic duals, without a finite-dimensionality assumption. -/
def complementaryBettiDualEquiv (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (p q : ℕ) (hpq : p + q = 2 * V.complexDimension) :
    V.rationalCohomology p ≃ₗ[ℚ] Module.Dual ℚ (V.rationalCohomology q) :=
  (AlgebraicTopology.Cohomology.Singular.UniversalCoefficient.singularUniversalCoefficientEquiv (F := ℚ)
    (TopCat.of V.analyticSpace) p).trans
      (V.poincareDuality q p (by omega)).toLinearEquiv.dualMap

/-- Every rational Betti group of a smooth projective variety is finite
dimensional. In complementary degrees, two dualities give a double-dual
equivalence; above real dimension, Poincare duality gives vanishing. -/
theorem rationalCohomology_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (n : ℕ) : FiniteDimensional ℚ (V.rationalCohomology n) := by
  by_cases hn : n ≤ 2 * V.complexDimension
  · let q := 2 * V.complexDimension - n
    let e := complementaryBettiDualEquiv V n q (by dsimp [q]; omega)
    let f := complementaryBettiDualEquiv V q n (by dsimp [q]; omega)
    exact finiteDimensional_of_doubleDualEquiv _ (e.trans f.dualMap.symm)
  · let : Subsingleton (V.rationalCohomology n) :=
      ModuleCat.subsingleton_of_isZero
        (AlgebraicTopology.Duality.Poincare.Manifold.compactComplexManifold_singularCohomology_isZero
          V.complexDimension (M := V.analyticSpace) n (by omega))
    infer_instance

/-- Canonical coefficient extension is an isomorphism in every degree,
using the finite-dimensionality just proved from the variety itself. -/
def bettiComplexificationEquiv (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology n) ≃ₗ[ℂ] V.complexCohomology n := by
  let : FiniteDimensional ℚ (V.rationalCohomology n) :=
    rationalCohomology_finiteDimensional V n
  exact ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace V.toOver) n

/-- No arbitrary comparison is chosen: the equivalence is coefficient extension. -/
theorem bettiComplexificationEquiv_toLinearMap
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    (bettiComplexificationEquiv V n).toLinearMap =
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) n := by
  rfl

/-- The conjugation on the actual complexification agrees with conjugation
of singular-cochain values under canonical coefficient extension. -/
theorem complexification_conjugation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) =
    ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
      rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      exact (((ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V).map_smulₛₗ z
        (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace V.toOver) 1 c)).trans
          (congrArg (fun y : V.complexCohomology 1 => star z • y)
            (ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace V.toOver) c))).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The geometric Hodge pieces satisfy exactly the conjugation condition
required by the statement's rational weight-one Hodge structure. -/
theorem geometricH1_conjugate_mem (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x ∈
      (V.pureBettiSubspace 0 1).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1) ↔
    x ∈ (V.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1) := by
  constructor
  · intro hx
    have h := ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic V _ hx
    rw [← complexification_conjugation, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at h
    exact h
  · intro hx
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) ∈ V.pureBettiSubspace 0 1
    rw [complexification_conjugation]
    exact ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_holomorphic V _ hx

/-- Coefficient extension commutes with the actual pullback on Betti groups. -/
theorem complexification_pullback {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (a : V.toOver ⟶ W.toOver) (n : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (W.rationalCohomology n)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) n
        ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n a).hom.baseChange ℂ x) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n a
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace W.toOver) n x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z c =>
      simp only [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      exact (congrArg (fun y : V.complexCohomology n => z • y)
        (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality a n) c)).trans
          ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n a).hom.map_smul z _).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Surjectivity of the actual de Rham pullback descends through the canonical
comparison and faithful coefficient extension to rational Betti cohomology. -/
theorem rationalBettiPullback_surjective_of_deRham {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (a : V.toOver ⟶ W.toOver) (n : ℕ)
    (ha : Function.Surjective (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a n)) :
    Function.Surjective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n a).hom := by
  have hc : Function.Surjective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n a) := by
    intro c
    obtain ⟨d, hd⟩ := ha ((V.deRhamBettiIso n).inv c)
    refine ⟨(W.deRhamBettiIso n).hom d, ?_⟩
    have h := ConcreteCategory.congr_hom
      (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamBettiIso_naturality a n) d
    change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n a ((W.deRhamBettiIso n).hom d) =
      (V.deRhamBettiIso n).hom (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamPullback a n d) at h
    rw [h, hd]
    exact (V.deRhamBettiIso n).toLinearEquiv.apply_symm_apply c
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective ℚ ℂ
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n a).hom).mp
  change Function.Surjective ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n a).hom.baseChange ℂ)
  intro u
  obtain ⟨y, hy⟩ := hc (bettiComplexificationEquiv V n u)
  refine ⟨(bettiComplexificationEquiv W n).symm y, ?_⟩
  apply (bettiComplexificationEquiv V n).injective
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) n
    ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n a).hom.baseChange ℂ
      ((bettiComplexificationEquiv W n).symm y)) = bettiComplexificationEquiv V n u
  rw [complexification_pullback]
  change Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n a
    (bettiComplexificationEquiv W n ((bettiComplexificationEquiv W n).symm y)) = _
  rw [LinearEquiv.apply_symm_apply]
  exact hy

/-- Algebraic pullback preserves each geometric Hodge piece on the actual
complexification of rational cohomology. -/
theorem pullback_mem_geometricHodgePiece {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (a : V.toOver ⟶ W.toOver) (p q : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (W.rationalCohomology (p + q)))
    (hx : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace W.toOver) (p + q) x ∈
      W.pureBettiSubspace p q) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (p + q)
        ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) (p + q) a).hom.baseChange ℂ x) ∈
      V.pureBettiSubspace p q := by
  rw [complexification_pullback]
  exact Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace a p q hx

/-- Once the geometric Hodge structures have been constructed, compatibility
of algebraic pullback follows from the proved pure-form naturality. -/
theorem pullback_isHodgeMap {V W : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (a : V.toOver ⟶ W.toOver)
    (HV : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1))
    (HW : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (W.rationalCohomology 1))
    (hV : IsCanonicalH1 V HV) (hW : IsCanonicalH1 W HW) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap HW HV (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom := by
  intro x hx
  rw [hV.1]
  rw [hW.1] at hx
  exact pullback_mem_geometricHodgePiece a 1 0 x hx

/-- A bijective rational Hodge map has a Hodge inverse: its complexification
is block diagonal for the two direct-sum decompositions. -/
theorem hodgeMap_inverse
    {U V : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (K : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)
    (e : U ≃ₗ[ℚ] V) (he : ComplexMultiplication.WeightOne.CM.IsHodgeMap H K e.toLinearMap) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap K H e.symm.toLinearMap := by
  intro y hy
  change (e.symm.baseChange ℚ ℂ V U) y ∈ H.holomorphic
  rw [LinearEquiv.baseChange_symm]
  let ec := e.baseChange ℚ ℂ U V
  obtain ⟨u, v, huv, _⟩ := Submodule.existsUnique_add_of_isCompl
    H.complementary (ec.symm y)
  have hu : ec u ∈ K.holomorphic := he u u.property
  have hv : ec v ∈ K.antiholomorphic := he.map_antiholomorphic v.property
  have hadd : ec u + ec v = y := by
    rw [← map_add, huv, ec.apply_symm_apply]
  have hvh : ec v ∈ K.holomorphic := by
    rw [eq_sub_of_add_eq' hadd]
    exact K.holomorphic.sub_mem hy hu
  have hvzero : ec v = 0 :=
    (Submodule.disjoint_def.mp K.complementary.disjoint) _ hvh hv
  have hvzero' : (v : ComplexMultiplication.WeightOne.CM.Complexification U) = 0 :=
    ec.injective (hvzero.trans ec.map_zero.symm)
  change ec.symm y ∈ H.holomorphic
  rw [← huv, hvzero', add_zero]
  exact u.property

/-- Two pointed algebraic Albanese varieties are isomorphic compatibly with
the maps from X. This follows only from the stated universal properties. -/
theorem exists_albanese_comparison
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver) (b : X.toOver ⟶ B.toOver)
    (ha : IsAlbaneseMap X x₀ A a) (hb : IsAlbaneseMap X x₀ B b) :
    ∃ e : A.toOver ≅ B.toOver,
      IsMonHom e.hom ∧ IsMonHom e.inv ∧
      a ≫ e.hom = b ∧ b ≫ e.inv = a := by
  obtain ⟨g, hg, _⟩ := ha.2 B b hb.1
  obtain ⟨h, hh, _⟩ := hb.2 A a ha.1
  let : IsMonHom g := hg.1
  let : IsMonHom h := hh.1
  have hgh : g ≫ h = 𝟙 A.toOver := by
    apply (ha.2 A a ha.1).unique
    · exact ⟨inferInstance, by rw [← Category.assoc, hg.2, hh.2]⟩
    · exact ⟨inferInstance, Category.comp_id a⟩
  have hhg : h ≫ g = 𝟙 B.toOver := by
    apply (hb.2 B b hb.1).unique
    · exact ⟨inferInstance, by rw [← Category.assoc, hh.2, hg.2]⟩
    · exact ⟨inferInstance, Category.comp_id b⟩
  exact ⟨⟨g, h, hgh, hhg⟩, hg.1, hh.1, hg.2, hh.2⟩

/-- Contravariant Betti comparison for an actual isomorphism of varieties. -/
def bettiEquivOfIso (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : A.toOver ≅ B.toOver) :
    B.variety.rationalCohomology 1 ≃ₗ[ℚ] A.variety.rationalCohomology 1 :=
  ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).mapIso e.op).toLinearEquiv

/-- The comparison uses the actual pullback induced by the scheme morphism. -/
theorem bettiEquivOfIso_toLinearMap
    (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (e : A.toOver ≅ B.toOver) :
    (bettiEquivOfIso A B e).toLinearMap =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 e.hom).hom := by
  rfl

/-- The actual holomorphic and antiholomorphic Betti pieces have zero intersection. -/
theorem pureBetti_one_disjoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Disjoint (V.pureBettiSubspace 1 0) (V.pureBettiSubspace 0 1) := by
  apply Submodule.disjoint_def.mpr
  intro c hc hd
  obtain ⟨x, hx, hxc⟩ := hc
  obtain ⟨y, hy, hyc⟩ := hd
  have hxy : x = y := (V.deRhamBettiIso 1).toLinearEquiv.injective (hxc.trans hyc.symm)
  have hz : x = 0 := Submodule.disjoint_def.mp
    (ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.pureDeRham_one_disjoint (E := V.analyticModel) (M := V.analyticSpace))
      x hx (hxy.symm ▸ hy)
  rw [← hxc, hz, map_zero]

/-- Disjointness also holds for the prescribed subspaces of complexified rational H¹. -/
theorem geometricH1_disjoint (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Disjoint ((V.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1))
      ((V.pureBettiSubspace 0 1).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  apply (bettiComplexificationEquiv V 1).injective
  rw [map_zero]
  exact Submodule.disjoint_def.mp (pureBetti_one_disjoint V) _ hx hy

/-- The prescribed geometric Hodge pieces span the actual complexified rational H¹. -/
theorem geometricH1_sup_top (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (V.pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1) ⊔
    (V.pureBettiSubspace 0 1).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1) = ⊤ := by
  let e := bettiComplexificationEquiv V 1
  apply top_unique
  intro x _
  have hx : e x ∈ V.pureBettiSubspace 1 0 ⊔ V.pureBettiSubspace 0 1 := by
    rw [ComplexMultiplication.HodgeComparison.OneSpanning.CM.Construction.pureBetti_one_sup_top]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
  apply Submodule.mem_sup.mpr
  refine ⟨e.symm a, ?_, e.symm b, ?_, ?_⟩
  · change e (e.symm a) ∈ V.pureBettiSubspace 1 0
    simpa only [e.apply_symm_apply] using ha
  · change e (e.symm b) ∈ V.pureBettiSubspace 0 1
    simpa only [e.apply_symm_apply] using hb
  · rw [← map_add, hab, e.symm_apply_apply]

/-- The canonical rational weight-one Hodge structure exists for every projective variety. -/
def canonicalH1 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1) where
  finiteDimensional := rationalCohomology_finiteDimensional V 1
  holomorphic := (V.pureBettiSubspace 1 0).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
  antiholomorphic := (V.pureBettiSubspace 0 1).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
  complementary := ⟨geometricH1_disjoint V, codisjoint_iff.mpr (geometricH1_sup_top V)⟩
  conjugate_mem := geometricH1_conjugate_mem V

theorem canonicalH1_isCanonical (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : IsCanonicalH1 V (canonicalH1 V) :=
  ⟨rfl, rfl⟩

/-- The actual rational Kähler cup pairing produces a polarization in positive dimension. -/
theorem canonicalH1_polarizable_of_positive_dimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (k : ℕ)
    (hdim : k + 1 = Module.finrank ℂ V.analyticModel) :
    Nonempty (ComplexMultiplication.CM.Polarization.WeightOnePolarization (canonicalH1 V)) := by
  let : FiniteDimensional ℚ (V.rationalCohomology (2 + (k + k))) :=
    rationalCohomology_finiteDimensional V _
  let T : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology (2 + (k + k))) →ₗ[ℂ] ℂ :=
    (ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace V k).comp
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k)))
  apply ComplexMultiplication.HodgeComparison.PolarizationFromRationalPairing.CM.Construction.exists_polarization_of_positive_rational_pairing (canonicalH1 V)
    (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.rationalH1TopCup V k) (ComplexMultiplication.HodgeComparison.TopAlternating.CM.Construction.rationalH1TopCup_self V k) ?_ T ?_ ?_
  · intro u hu v hv
    apply (bettiComplexificationEquiv V (2 + (k + k))).injective
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))
      (LinearMap.BilinMap.baseChange ℂ (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.rationalH1TopCup V k) u v) =
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k)) 0
    rw [ComplexMultiplication.HodgeComparison.CupScalarExtension.CM.Construction.rationalH1TopCup_scalarExtension, map_zero]
    exact ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.complexH1TopCup_holomorphic_zero V k hdim _ _ hu hv
  · intro w
    change (ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace V k
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))
        ((1 : ℂ) ⊗ₜ[ℚ] w))).im = 0
    rw [ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul, one_smul]
    exact ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace_rational_real V k w
  · intro u hu hne
    change 0 < (Complex.I * ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace V k
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) (2 + (k + k))
        (LinearMap.BilinMap.baseChange ℂ (ComplexMultiplication.HodgeComparison.TopCup.CM.Construction.rationalH1TopCup V k) u
          (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) u)))).re
    rw [ComplexMultiplication.HodgeComparison.CupScalarExtension.CM.Construction.rationalH1TopCup_scalarExtension, complexification_conjugation]
    apply ComplexMultiplication.HodgeComparison.KahlerTopTrace.CM.Construction.fubiniStudyTopTrace_holomorphic_positive V k hdim _ hu
    intro hz
    apply hne
    exact (bettiComplexificationEquiv V 1).injective (hz.trans (map_zero _).symm)

/-- The canonical rational H¹ Hodge structure of every projective variety is polarizable. -/
theorem canonicalH1_polarizable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    Nonempty (ComplexMultiplication.CM.Polarization.WeightOnePolarization (canonicalH1 V)) := by
  by_cases hd : V.complexDimension = 0
  · let : Subsingleton (V.rationalCohomology 1) :=
      ModuleCat.subsingleton_of_isZero
        (AlgebraicTopology.Duality.Poincare.Manifold.compactComplexManifold_singularCohomology_isZero
          V.complexDimension (M := V.analyticSpace) 1 (by omega))
    let : Subsingleton (ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) := inferInstance
    refine ⟨ComplexMultiplication.HodgeComparison.PolarizationFromPositiveForm.CM.Construction.weightOnePolarizationOfPositive (canonicalH1 V) 0 (fun _ => rfl) ?_ ?_⟩
    · intro u _ v _
      simp
    · intro u _ hu
      exact False.elim (hu (Subsingleton.elim u 0))
  · apply canonicalH1_polarizable_of_positive_dimension V (V.complexDimension - 1)
    rw [V.analyticModel_complex_finrank]
    omega

def canonicalH1Polarization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) : ComplexMultiplication.CM.Polarization.WeightOnePolarization (canonicalH1 V) :=
  Classical.choice (canonicalH1_polarizable V)

/-- The actual period torus used by the constructed map is projective. -/
theorem rationalH1PeriodTorus_projective {Index : Type} [Fintype Index] [DecidableEq Index]
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (b : Module.Basis Index ℚ (V.rationalCohomology 1)) :
    Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.IsProjectiveComplexTorus (ComplexMultiplication.HodgeComparison.PeriodLattice.CM.Construction.RationalH1PeriodSpace V b) (ComplexMultiplication.HodgeComparison.PeriodLattice.CM.Construction.rationalPeriodLattice V b).toAddSubgroup :=
  ComplexMultiplication.HodgeComparison.PeriodTorusProjective.CM.Construction.rationalPeriodTorus_projective_of_polarization V b (canonicalH1 V) rfl (canonicalH1Polarization V)

def canonicalH1ProjectivePeriodData {Index : Type} [Fintype Index] [DecidableEq Index]
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (b : Module.Basis Index ℚ (V.rationalCohomology 1)) :
    HodgeConjecture.CMVariety.ProjectiveTorusData.CM.Abelian.ProjectivePeriodData :=
  ComplexMultiplication.HodgeComparison.PeriodTorusProjective.CM.Construction.rationalH1ProjectivePeriodData V b (canonicalH1 V) rfl (canonicalH1Polarization V)

/-- Every projective variety has an algebraic map to an abelian variety
whose actual rational H¹ pullback is surjective. -/
theorem exists_abelian_map_rationalH1_surjective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ∃ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (g : V.toOver ⟶ B.toOver),
      Function.Surjective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 g).hom := by
  let : FiniteDimensional ℚ (V.rationalCohomology 1) := rationalCohomology_finiteDimensional V 1
  obtain ⟨B, g, hg⟩ := ComplexMultiplication.HodgeComparison.AlgebraicPeriodMap.CM.Construction.exists_algebraic_period_map_h1_surjective V
    (Module.finBasis ℚ (V.rationalCohomology 1)) (canonicalH1 V) rfl (canonicalH1Polarization V)
  exact ⟨B, g, rationalBettiPullback_surjective_of_deRham g 1 hg⟩

/-- Translating the abelian target makes the constructed map pointed
and preserves surjectivity of its actual rational H¹ pullback. -/
theorem exists_pointed_abelian_map_rationalH1_surjective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver) :
    ∃ (B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (g : X.toOver ⟶ B.toOver),
      x₀ ≫ g = η[B.toOver] ∧
      Function.Surjective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 g).hom := by
  obtain ⟨B, f, hf⟩ := exists_abelian_map_rationalH1_surjective X
  let t : B.toOver ≅ B.toOver := GrpObj.mulRight ((x₀ ≫ f)⁻¹)
  refine ⟨B, f ≫ t.hom, ?_, ?_⟩
  · rw [← Category.assoc]
    change (x₀ ≫ f) ≫ (𝟙 B.toOver *
      (CartesianMonoidalCategory.toUnit B.toOver ≫ (x₀ ≫ f)⁻¹)) = η[B.toOver]
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc,
      CartesianMonoidalCategory.comp_toUnit, CartesianMonoidalCategory.toUnit_unit,
      Category.id_comp, mul_inv_cancel]
    simp only [Hom.one_def, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
  · intro c
    obtain ⟨z, hz⟩ := hf c
    obtain ⟨w, hw⟩ := (bettiEquivOfIso B B t).surjective z
    change (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 t.hom).hom w = z at hw
    refine ⟨w, ?_⟩
    change Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback (f ≫ t.hom) 1 w = c
    rw [Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp f t.hom 1, ModuleCat.comp_apply]
    exact (congrArg (fun v => (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom v) hw).trans hz

/-- Albanese universality factors the constructed pointed period map,
forcing surjectivity of the actual Albanese pullback on rational H¹. -/
theorem albanese_h1_pullback_surjective (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (a : X.toOver ⟶ A.toOver) (ha : IsAlbaneseMap X x₀ A a) :
    Function.Surjective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom := by
  obtain ⟨B, g, hg, hs⟩ := exists_pointed_abelian_map_rationalH1_surjective X x₀
  obtain ⟨h, hh, _⟩ := ha.2 B g hg
  intro c
  obtain ⟨z, hz⟩ := hs c
  refine ⟨(Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 h).hom z, ?_⟩
  have hc := ConcreteCategory.congr_hom
    (Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalBettiPullback_comp a h 1) z
  rw [hh.2] at hc
  exact hc.symm.trans hz

/-- HodgeComparison: the actual Albanese pullback is an isomorphism of the canonical
rational H¹ Hodge structures, for every smooth projective connected variety. -/
theorem albanese_h1_hodge_iso
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x₀ : 𝟙_ (Over Foundations.Scheme.ProjectiveSpace.complexBase) ⟶ X.toOver)
    (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (a : X.toOver ⟶ A.toOver)
    (ha : IsAlbaneseMap X x₀ A a) :
    ∃ (HA : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (A.variety.rationalCohomology 1))
      (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
      (e : A.variety.rationalCohomology 1 ≃ₗ[ℚ]
        X.rationalCohomology 1),
      IsCanonicalH1 A.variety HA ∧
      IsCanonicalH1 X HX ∧
      e.toLinearMap = (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap HA HX e.toLinearMap ∧
      ComplexMultiplication.WeightOne.CM.IsHodgeMap HX HA e.symm.toLinearMap := by
  let e := LinearEquiv.ofBijective (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom
    ⟨albanese_h1_pullback_injective X x₀ A a ha,
      albanese_h1_pullback_surjective X x₀ A a ha⟩
  have he : ComplexMultiplication.WeightOne.CM.IsHodgeMap (canonicalH1 A.variety) (canonicalH1 X) e.toLinearMap :=
    pullback_isHodgeMap a (canonicalH1 X) (canonicalH1 A.variety)
      (canonicalH1_isCanonical X) (canonicalH1_isCanonical A.variety)
  exact ⟨canonicalH1 A.variety, canonicalH1 X, e, canonicalH1_isCanonical A.variety,
    canonicalH1_isCanonical X, rfl, he, hodgeMap_inverse _ _ e he⟩

/-- All geometric de Rham cohomology groups are finite-dimensional. -/
theorem deRhamCohomology_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    FiniteDimensional ℂ (V.deRhamCohomology n) := by
  let : FiniteDimensional ℚ (V.rationalCohomology n) := rationalCohomology_finiteDimensional V n
  let e := (V.deRhamBettiIso n).toLinearEquiv.trans (bettiComplexificationEquiv V n).symm
  exact FiniteDimensional.of_injective e.toLinearMap e.injective

/-- Closed holomorphic one-forms form a finite-dimensional vector space. -/
theorem holomorphic_closedForms_finiteDimensional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    FiniteDimensional ℂ (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0) := by
  let : FiniteDimensional ℂ (V.deRhamCohomology 1) := deRhamCohomology_finiteDimensional V 1
  exact FiniteDimensional.of_injective
    (AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureFormClass V.analyticModel V.analyticSpace 1 0)
    ComplexMultiplication.HodgeComparison.HolomorphicPrimitive.CM.Construction.holomorphic_formClass_injective

end

end OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs.CM.Construction
