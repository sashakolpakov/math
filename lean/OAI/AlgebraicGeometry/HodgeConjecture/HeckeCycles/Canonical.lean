import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.OneSpanning
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Intersection
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.BettiConjugation
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation
import OAI.AlgebraicTopology.Kunneth.ProjectiveFinitenessLe

/-! # Canonical -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Canonical.CM

noncomputable section

/-! Construct the reference variety's canonical rational weight-one
Hodge structure from its actual Hodge decomposition and Betti conjugation. -/

open scoped Classical TensorProduct _root_.Manifold ContDiff

theorem complexification_conjugation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
      (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) =
        ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 x) := by
  induction x using TensorProduct.inductionOn with
  | tmul z x =>
      rw [ComplexMultiplication.WeightOne.CM.coefficientConjugation_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
      let a : V.complexCohomology 1 :=
        AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace V.toOver) 1 x
      change star z • a = ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 V (z • a)
      rw [map_smulₛₗ]
      exact congrArg (fun y => star z • y)
        (ComplexMultiplication.HodgeComparison.PositiveCohomologyConjugation.CM.Construction.conjugateSimplicialH1_rational (Betti.Scheme.schemePointSpace V.toOver) x).symm
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The reference Hodge structure is derived from projective geometry;
neither its existence nor its canonical subspaces are new inputs. -/
def canonicalHodge (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (V.rationalCohomology 1) where
  finiteDimensional := AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite V 1
  holomorphic := (V.pureBettiSubspace 1 0).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
  antiholomorphic := (V.pureBettiSubspace 0 1).comap
    (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1)
  complementary := by
    let : FiniteDimensional ℚ (V.rationalCohomology 1) :=
      AlgebraicTopology.Kunneth.ProjectiveFinitenessLe.Construction.ProjectiveFiniteness.integralProjective_cohomology_finite V 1
    have hd : IsCompl (V.pureDeRhamSubspace 1 0) (V.pureDeRhamSubspace 0 1) :=
      ⟨ComplexMultiplication.HodgeComparison.Intersection.CM.Construction.pureDeRham_one_disjoint, codisjoint_iff.mpr (ComplexMultiplication.HodgeComparison.OneSpanning.CM.Construction.pureDeRham_one_sup_top V)⟩
    have hb : IsCompl (V.pureBettiSubspace 1 0) (V.pureBettiSubspace 0 1) :=
      (Submodule.orderIsoMapComap (V.deRhamBettiIso 1).toLinearEquiv).isCompl_iff.mp hd
    exact (Submodule.orderIsoMapComap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexificationEquiv (Betti.Scheme.schemePointSpace V.toOver) 1)).symm.isCompl_iff.mp hb
  conjugate_mem x := by
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1
        (ComplexMultiplication.WeightOne.CM.coefficientConjugation (V.rationalCohomology 1) x) ∈ V.pureBettiSubspace 0 1 ↔
      ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 x ∈ V.pureBettiSubspace 1 0
    constructor
    · intro hx
      have h := ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_antiholomorphic V _ hx
      rw [← complexification_conjugation, ComplexMultiplication.WeightOne.CM.coefficientConjugation_involutive] at h
      exact h
    · intro hx
      rw [complexification_conjugation]
      exact ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1_holomorphic V _ hx

theorem pullback_canonical
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : C(X.analyticSpace, Y.analyticSpace))
    (hf : ContMDiff 𝓘(ℂ, X.analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f) :
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (canonicalHodge Y) (canonicalHodge X) (AnalyticPullback.CM.pullbackQ f 1).hom :=
  AnalyticPullback.CM.pullback_isHodgeMap f hf (canonicalHodge X) (canonicalHodge Y) rfl rfl

theorem represented_class_holomorphic (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (form : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms V.analyticModel V.analyticSpace 1 0)
    (θ : ComplexMultiplication.WeightOne.CM.Complexification (V.rationalCohomology 1))
    (hθ : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 θ =
      (V.deRhamBettiIso 1).hom (V.deRhamClass 1 form.val)) :
    θ ∈ (canonicalHodge V).holomorphic := by
  change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace V.toOver) 1 θ ∈ V.pureBettiSubspace 1 0
  rw [hθ, ← V.clayHodgeToBetti_projection 1 0 form, ← V.clayHodgeToBetti_range 1 0]
  exact LinearMap.mem_range_self _ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Canonical.CM
