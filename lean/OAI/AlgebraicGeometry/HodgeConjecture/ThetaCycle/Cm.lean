import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource
import OAI.AlgebraicGeometry.ComplexMultiplication.RealizedHodgeMaps
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental
import OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients
import OAI.AlgebraicTopology.Products.CupCohomology

/-! # Cm -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm

noncomputable section

/-!
Native geometric interfaces for ThetaCycle. A surface is an actual integral smooth
projective scheme of complex dimension two. Its fundamental class is the
constructed complex-oriented integral class, extended to complex coefficients;
evaluation is the genuine singular homology/cohomology pairing.
Principal refinements retain the literal ball uniformizations, algebraic map,
finite covering degree, and the integral fundamental-class degree law. These
are output data in ThetaCycle, not hypotheses granting its missing surface.
-/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.CompactManifoldFundamental.Cycles OAI.AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients

/-- Actual cup product on complex Betti cohomology. -/
abbrev cup (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :=
  AlgebraicTopology.Products.CupCohomology.singularCohomologyCup
    (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) p q

/-- The source's surface condition uses the derived algebraic dimension. -/
abbrev ProjectiveSurface :=
  {X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety // X.complexDimension = 2}

namespace ProjectiveSurface

abbrev variety (S : ProjectiveSurface) : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety := S.val

/-- The canonical integral fundamental class, transported only in degree. -/
def integralClass (S : ProjectiveSurface) :
    (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (Betti.Scheme.schemePointSpace S.variety.toOver)).homology 4 :=
  (eqToHom (congrArg
    (fun n => (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains
      (Betti.Scheme.schemePointSpace S.variety.toOver)).homology n)
    (show 2 * S.variety.complexDimension = 4 by rw [S.property])))
      (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass
        S.variety.complexDimension S.variety.analyticSpace)

/-- The same class with complex coefficients; no class is supplied as input. -/
def fundamentalClass (S : ProjectiveSurface) :
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℂ)
      (Betti.Scheme.schemePointSpace S.variety.toOver)).homology 4 :=
  AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ)
    (Betti.Scheme.schemePointSpace S.variety.toOver) 4 S.integralClass

/-- Actual evaluation on the complex-oriented fundamental class. -/
def evaluate (S : ProjectiveSurface) :
    S.variety.complexCohomology 4 →ₗ[ℂ] ℂ :=
  (LinearMap.applyₗ' ℂ S.fundamentalClass).comp
    (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ)
      (Betti.Scheme.schemePointSpace S.variety.toOver) 4)

theorem evaluate_eq (S : ProjectiveSurface)
    (z : S.variety.complexCohomology 4) :
    S.evaluate z =
      AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ)
        (Betti.Scheme.schemePointSpace S.variety.toOver) 4 z
        (AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology (R := ℂ)
          (Betti.Scheme.schemePointSpace S.variety.toOver) 4 S.integralClass) := rfl

end ProjectiveSurface

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

/-- The actual principal quotient of the specified rank-three Hermitian ball. -/
structure PrincipalBallSurface (B : HeckeCycles.GeometricSource.CM.BallDatum K) (N : ℕ) where
  surface : ProjectiveSurface
  torsion_free : ∀ g : HeckeCycles.GeometricSource.CM.Vec K ≃ₗ[K] HeckeCycles.GeometricSource.CM.Vec K,
    B.principalLevel N g → ∀ k : ℕ, 0 < k → g ^ k = 1 → g = 1
  projection : B.Domain → surface.variety.analyticSpace
  isBallCover : B.IsBallCover N surface.variety projection

/-- A common deeper congruence cover, retaining its geometric degree law.
The degree law is about the canonical integral classes, not an arbitrary
linear functional. Existence of this record remains part of the main target. -/
structure PrincipalRefinement {B : HeckeCycles.GeometricSource.CM.BallDatum K}
    {N M : ℕ} (S : PrincipalBallSurface K B N)
    (T : PrincipalBallSurface K B M) where
  divides : N ∣ M
  map : T.surface.variety.toOver ⟶ S.surface.variety.toOver
  over_ball : ∀ z : B.Domain,
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map map) (T.projection z) = S.projection z
  covering : IsCoveringMap (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map map)
  degree : ℕ
  degree_pos : 0 < degree
  fibers : ∀ x : S.surface.variety.analyticSpace,
    Nat.card {y : T.surface.variety.analyticSpace //
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map map) y = x} = degree
  integral_degree :
    HomologicalComplex.homologyMap
      (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map map)) 4
      T.surface.integralClass = degree • S.surface.integralClass

namespace PrincipalRefinement

variable {K} {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N M : ℕ}
  {S : PrincipalBallSurface K B N} {T : PrincipalBallSurface K B M}

omit [IsGalois ℚ K] in
/-- Extension of coefficients preserves the actual covering degree law. -/
theorem fundamentalClass_map (p : PrincipalRefinement K S T) :
    AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularHomologyPushforward (R := ℂ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map p.map) 4 T.surface.fundamentalClass =
        (p.degree : ℂ) • S.surface.fundamentalClass := by
  unfold ProjectiveSurface.fundamentalClass
  rw [AlgebraicTopology.Duality.Poincare.IntegralHomologyCoefficients.integralToScalarSingularHomology_naturality,
    p.integral_degree, map_nsmul, Nat.cast_smul_eq_nsmul]

omit [IsGalois ℚ K] in
/-- ThetaCoverDegree's degree scaling in the native Betti/fundamental-class interface. -/
theorem evaluate_pullback (p : PrincipalRefinement K S T)
    (z : S.surface.variety.complexCohomology 4) :
    T.surface.evaluate
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 p.map z) =
      (p.degree : ℂ) * S.surface.evaluate z := by
  change AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℂ ℂ)
    (Betti.Scheme.schemePointSpace T.surface.variety.toOver) 4
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback (ModuleCat.of ℂ ℂ)
      (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map p.map) 4 z) T.surface.fundamentalClass = _
  rw [AlgebraicTopology.Cohomology.Singular.EvaluationNaturality.singularEvaluation_naturality, p.fundamentalClass_map, map_smul]
  rfl

omit [IsGalois ℚ K] in
/-- A common finite cover preserves nonvanishing of the actual evaluation. -/
theorem evaluate_pullback_ne_zero (p : PrincipalRefinement K S T)
    (z : S.surface.variety.complexCohomology 4)
    (hz : S.surface.evaluate z ≠ 0) :
    T.surface.evaluate
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 4 p.map z) ≠ 0 := by
  rw [p.evaluate_pullback]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt p.degree_pos)) hz

end PrincipalRefinement

/-- The original rational-Hodge-map span remains available for extraction. -/
def cmLineSpan
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (HX : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (τ : Gal(K/ℚ)) :
    Submodule ℂ (X.complexCohomology 1) :=
  Submodule.span ℂ
    {z | ∃ u : K →ₗ[ℚ] X.rationalCohomology 1,
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K v) HX u ∧
      z = ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification
        (Betti.Scheme.schemePointSpace X.toOver) 1
        (u.baseChange ℂ
          (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ)))}

/-- Finite complex linear combinations of wedges from two spaces. -/
def wedgeSpan
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (S T : Submodule ℂ (X.complexCohomology 1)) :
    Submodule ℂ (X.complexCohomology 2) :=
  Submodule.span ℂ
    {z | ∃ a ∈ S, ∃ b ∈ T, z = cup X 1 1 a b}

/-- The four prescribed embedding classes, pulled back by algebraic maps. -/
def fourClass
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : (i : Fin 4) → X.toOver ⟶ (R i).abelianVariety.toOver) :
    X.complexCohomology 4 :=
  let b : Fin 4 → X.complexCohomology 1 := fun i =>
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i)
      ((R i).complexComparison
        (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K
          (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K))))
  cup X 2 2 (cup X 1 1 (b 0) (b 1)) (cup X 1 1 (b 2) (b 3))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm
