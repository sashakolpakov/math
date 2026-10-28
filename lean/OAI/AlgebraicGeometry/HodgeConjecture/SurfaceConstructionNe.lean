import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionQ
import OAI.AlgebraicGeometry.HodgeConjecture.Pairs
import OAI.AlgebraicGeometry.HodgeConjecture.TensorContraction
import OAI.AlgebraicGeometry.HodgeConjecture.Intersections
import OAI.AlgebraicGeometry.HodgeConjecture.Correspondence
import OAI.AlgebraicGeometry.HodgeConjecture.Connected
import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceScalar
import OAI.AlgebraicGeometry.HodgeConjecture.Normalize
import OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionOne

/-! # Surface Construction Ne -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionNe.CM

noncomputable section

/-!
Complete proof of the unchanged SurfaceConstruction conclusion, conditional on the explicit
ScalarDescent, DegreeTwo, repaired ThetaCycle, ChernClass, Functoriality, ThomClass, and strengthened ProjectionFormula input propositions.
Kunneth, canonical Poincare duality, and the cohomological projection formula
are used through their checked native proofs.

The exact target tensor is proved nonzero. Four opposite-embedding divisor
classes give an algebraic correspondence on the genuine product S × X.
Its actual coefficient class is the exterior cup of the source and target
fourfold classes. Canonical Functoriality pushforward is identified with ProjectionFormula's signed
Poincare definition, giving the precise surface projection formula.

Connected top-degree trace and Kunneth make the integration scalar nonzero
in E. Negating CM types changes only their rational markings; six exhaustive
even permutations normalize all identity-sign patterns. When no other place
exists, two divisor pairs give the elementary case. The final theorem below
retains the original product, comparison vectors, and finite-cycle conclusion.
-/

open _root_.CategoryTheory
open scoped TensorProduct

section

/-- Evaluation of coefficient-field cohomology on a rational homology
class lands in E, by the canonical scalar extension of rational evaluation. -/
def coefficientEvaluation (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)).homology n) :
    (E ⊗[ℚ] X.rationalCohomology n) →ₗ[E] E :=
  ((Algebra.linearMap ℚ E).comp
    ((AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver) n).flip z)).liftBaseChange E

/-- The native complex pairing equals the inclusion of its E-valued scalar. -/
theorem realizeCoefficient_evaluation (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)).homology n)
    (x : E ⊗[ℚ] X.rationalCohomology n) :
    ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace X.toOver) n
      (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n x) z = (coefficientEvaluation E X n z x : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
    rw [Coefficients.CM.SurfaceConstruction.realizeCoefficient_tmul]
    change ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace X.toOver) n
      ((a : ℂ) • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) n x) z = _
    rw [ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology_smul_rational]
    change (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver) n x z) •
      (a : ℂ) = ((a * algebraMap ℚ E
        (AlgebraicTopology.Cohomology.Singular.Evaluation.singularEvaluation (ModuleCat.of ℚ ℚ) (Betti.Scheme.schemePointSpace X.toOver) n x z) : E) : ℂ)
    simp [Algebra.smul_def, mul_comm]

theorem coefficientEvaluation_ne_zero (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (z : (AlgebraicTopology.Cohomology.Singular.Evaluation.singularScalarChains (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver)).homology n)
    (x : E ⊗[ℚ] X.rationalCohomology n)
    (hx : ComplexMultiplication.CohomologyBaseChange.CM.evaluateComplexOnRationalHomology (Betti.Scheme.schemePointSpace X.toOver) n
      (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n x) z ≠ 0) :
    coefficientEvaluation E X n z x ≠ 0 := by
  intro hz
  apply hx
  rw [realizeCoefficient_evaluation, hz, IntermediateField.coe_zero]

/-- Proper pushforward preserves the actual algebraic coefficient-class image. -/
theorem coefficientPushforward_algebraic (E : IntermediateField ℚ ℂ)
    (hFunctoriality : SurfaceConstructionQ.CM.ProperCycleClassCompatibility)
    {S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (f : S.toOver ⟶ X.toOver)
    (p q : ℕ) (hdeg : p + X.complexDimension = q + S.complexDimension)
    {x : E ⊗[ℚ] S.rationalCohomology (p + p)}
    (hx : x ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E S p) :
    (Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg).baseChange E x ∈
      Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X q := by
  obtain ⟨z, rfl⟩ := hx
  refine ⟨(Cycles.Functoriality.UnitCap.cyclePushforward f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg).baseChange E z, ?_⟩
  have hmaps : (X.geometricCycleClassMap q).comp
      (Cycles.Functoriality.UnitCap.cyclePushforward f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg) =
      (Cycles.Functoriality.UnitCap.cohomologyPushforward f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg).comp
        (S.geometricCycleClassMap p) := by
    apply LinearMap.ext
    intro w
    exact hFunctoriality f (SurfaceConstructionQ.CM.map_isProper f) p q hdeg w
  have h := congrArg (fun m => m.baseChange E z) hmaps
  simpa only [LinearMap.baseChange_comp, LinearMap.comp_apply] using h

/-- A finite algebraic divisor cycle realizes the literal native opposite
pair class on two independently supplied abelian realizations. -/
theorem oppositePair_has_finite_cycle
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    {U : Type} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    ∃ (n : ℕ) (a : Fin n → E) (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle P 1),
      (∑ j : Fin n, (a j : ℂ) • P.rationalCohomologyInclusion 2
        (P.geometricCycleClassMap 1 (Z j))) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πR (R.complexComparison (h.embeddingBasis τ)))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πT
          (T.complexComparison (h.embeddingBasis (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)))) := by
  obtain ⟨n, a, Z, hz⟩ := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_finite_sum E P 1
    (Pairs.CM.SurfaceConstruction.oppositePair_algebraic E hScalarDescent hDegreeTwo h R T P πR πT τ)
  refine ⟨n, a, Z, hz.trans ?_⟩
  rw [Pairs.CM.SurfaceConstruction.oppositePair, Pairs.CM.SurfaceConstruction.realizeCoefficient_h1Cup, Pairs.CM.SurfaceConstruction.pulledEmbeddingCoefficient_realize,
    Pairs.CM.SurfaceConstruction.pulledEmbeddingCoefficient_realize]

/-- The same finite-cycle statement for the exact canonical field vectors
used by the committed SurfaceConstruction specification. -/
theorem canonicalOppositePair_has_finite_cycle
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    ∃ (n : ℕ) (a : Fin n → E) (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle P 1),
      (∑ j : Fin n, (a j : ℂ) • P.rationalCohomologyInclusion 2
        (P.geometricCycleClassMap 1 (Z j))) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πR
          (R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ)))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πT
          (T.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)))) := by
  obtain ⟨n, a, Z, hz⟩ := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_finite_sum E P 1
    (Pairs.CM.SurfaceConstruction.normalizedOppositePair_algebraic E hScalarDescent hDegreeTwo h R T P πR πT τ)
  exact ⟨n, a, Z, hz.trans (Pairs.CM.SurfaceConstruction.normalizedOppositePair_realize E h R T P πR πT τ)⟩

/-- The actual surface correspondence realizes the opposite-labelled
fourfold class algebraically. Its scalar is proved nonzero by native
Kunneth and Poincare duality. -/
theorem surface_opposite_algebraic
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (hFunctoriality : SurfaceConstructionQ.CM.ProperCycleClassCompatibility)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (H : Fin 4 → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
    (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i)) (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (hS : S.complexDimension = 2) (hX : 2 ≤ X.complexDimension)
    (f : ∀ i, S.toOver ⟶ (R i).abelianVariety.toOver)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (τ : Fin 4 → E →ₐ[ℚ] ℂ)
    (ha : CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S f τ ≠ 0) :
    CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π (fun i => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i)) ∈
      Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 := by
  let W := Albanese.Construction.SegreClosed.tensorIntegralProjectiveVariety S X
  let pr : W.toOver ⟶ X.toOver := CartesianMonoidalCategory.snd S.toOver X.toOver
  let b := CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π (fun i => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (τ i))
  obtain ⟨r, hr, htrace⟩ := SurfaceScalar.CM.Construction.coefficientSurfaceTrace_scalar E S X hS
    (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S f τ) ha
  have hp := Correspondence.CM.SurfaceConstruction.surfaceCorrespondence_pushforward E H h R S X f π τ hS hX
  have htrace' := (SurfaceScalar.CM.Construction.coefficientSurfaceTrace_eq E S X hS
    (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S f τ)).symm.trans htrace
  have hcup : CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 4 0 b
      (r • ((1 : E) ⊗ₜ[ℚ] Cycles.Functoriality.UnitCap.cohomologyUnit X)) = r • b := by
    rw [map_smul, SurfaceScalar.CM.Construction.coefficientCup_unit_right]
  have hclass := hp.trans ((congrArg (CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 4 0 b) htrace').trans hcup)
  have halg := coefficientPushforward_algebraic E hFunctoriality (S := W) (X := X) pr 4 2
    (by dsimp [W]; rw [Products.CM.SurfaceConstruction.product_complexDimension, hS]; omega)
    (Correspondence.CM.SurfaceConstruction.surfaceCorrespondence_algebraic E H h R S X f π τ hScalarDescent hDegreeTwo hThomClass hProjectionFormula)
  exact Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_of_smul E X 2 r hr b (hclass ▸ halg)

/-- Coefficient conjugation changes the opposite labels back to the
original labels while retaining the actual algebraic cycle image. -/
theorem surface_algebraic
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (hFunctoriality : SurfaceConstructionQ.CM.ProperCycleClassCompatibility)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (H : Fin 4 → ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E)
    (h : ∀ i, ComplexMultiplication.WeightOne.CM.RankOneCMAction E (H i)) (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (H i))
    (S X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    [PathConnectedSpace S.analyticSpace] [PathConnectedSpace X.analyticSpace]
    (hS : S.complexDimension = 2) (hX : 2 ≤ X.complexDimension)
    (f : ∀ i, S.toOver ⟶ (R i).abelianVariety.toOver)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (τ : Fin 4 → E →ₐ[ℚ] ℂ)
    (ha : CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S f τ ≠ 0) :
    CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π τ ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 := by
  have hb := surface_opposite_algebraic E hScalarDescent hDegreeTwo hFunctoriality hThomClass hProjectionFormula H h R S X hS hX f π τ ha
  have hc := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_scalarConjugate E X 2 (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) hb
  rw [CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_conjugate] at hc
  simpa only [CanonicalCoefficients.CM.SurfaceConstruction.galoisCoefficientEmbedding_conjugation, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive] using hc

/-- Full SurfaceConstruction conclusion in the normalized non-elementary case supplied
by ThetaCycle. The surface and nonvanishing are derived from the full repaired
input proposition, including its covering and refinement clauses. -/
theorem normalized_switch_algebraic
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (hThetaCycle : Surface.CM.Construction.BallSurfaceSwitchInput E) (hFunctoriality : SurfaceConstructionQ.CM.ProperCycleClassCompatibility)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hbalance : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (hid : ∀ i, (v i).val 1 = true)
    (hother : ∃ τ : Gal(E/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (hprod : CategoryTheory.Limits.IsLimit (CategoryTheory.Limits.Fan.mk X.toOver π)) :
    let τ : Fin 4 → E →ₐ[ℚ] ℂ := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
      (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
    let t := SurfaceConstructionQ.CM.fourCup X (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
      ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (τ i))))
    t ≠ 0 ∧ ∃ (n : ℕ) (a : Fin n → E) (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X 2),
      (∑ j : Fin n, (a j : ℂ) • X.rationalCohomologyInclusion 4
        (X.geometricCycleClassMap 2 (Z j))) = t := by
  dsimp only
  let H := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)
  let h := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E (v i)
  let τ : Fin 4 → E →ₐ[ℚ] ℂ := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
    (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
  have ht := FourProduct.CM.SurfaceConstruction.canonical_switchTensor_ne_zero E v R X π hprod
  refine ⟨ht, ?_⟩
  let : PathConnectedSpace X.analyticSpace :=
    Connected.CM.SurfaceConstruction.fourAbelianProduct_pathConnected (fun i => (R i).abelianVariety) X π hprod
  have hX : 2 ≤ X.complexDimension := by
    have hd := Kunneth.CM.SurfaceConstruction.complex_degree_le X 4 _ ht
    omega
  obtain ⟨B, N, S, f, _, _, hn, _⟩ := hThetaCycle v hbalance hid hother R 1 Nat.one_pos
  let : PathConnectedSpace S.surface.variety.analyticSpace := Connected.CM.SurfaceConstruction.ballSurface_pathConnected E S
  have hreal : Coefficients.CM.SurfaceConstruction.realizeCoefficient E S.surface.variety 4
      (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S.surface.variety f τ) =
      ThetaCycle.Cm.fourClass E v R S.surface.variety f :=
    CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize E H h R S.surface.variety f τ
  have hsource : CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S.surface.variety f τ ≠ 0 := by
    intro hz
    apply hn
    rw [← hreal, hz, Pairs.CM.SurfaceConstruction.realizeCoefficient_zero, map_zero]
  have halg := surface_algebraic E hScalarDescent hDegreeTwo hFunctoriality hThomClass hProjectionFormula H h R
    S.surface.variety X S.surface.property hX f π τ hsource
  obtain ⟨n, a, Z, hz⟩ := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_finite_sum E X 2 halg
  exact ⟨n, a, Z, hz.trans (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize E H h R X π τ)⟩

/-- Discharge the normalized intermediate proposition using the full
ThetaCycle input when another place exists and divisor intersections otherwise. -/
theorem normalizedSwitchAlgebraicity_of_inputs
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (hThetaCycle : Surface.CM.Construction.BallSurfaceSwitchInput E) (hFunctoriality : SurfaceConstructionQ.CM.ProperCycleClassCompatibility)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula) :
    Normalize.CM.SurfaceConstruction.NormalizedSwitchAlgebraicity E := by
  intro v hbalance hid R X _ hX π
  let H := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)
  let h := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E (v i)
  let τ : Fin 4 → E →ₐ[ℚ] ℂ := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
    (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
  refine ⟨CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π τ, ?_,
    CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize E H h R X π τ⟩
  by_cases hother : ∃ g : Gal(E/ℚ), g ≠ 1 ∧ g ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
  · obtain ⟨B, N, S, f, _, _, hn, _⟩ := hThetaCycle v hbalance hid hother R 1 Nat.one_pos
    let : PathConnectedSpace S.surface.variety.analyticSpace := Connected.CM.SurfaceConstruction.ballSurface_pathConnected E S
    have hreal : Coefficients.CM.SurfaceConstruction.realizeCoefficient E S.surface.variety 4
        (CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S.surface.variety f τ) =
        ThetaCycle.Cm.fourClass E v R S.surface.variety f :=
      CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize E H h R S.surface.variety f τ
    have hsource : CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R S.surface.variety f τ ≠ 0 := by
      intro hz
      apply hn
      rw [← hreal, hz, Pairs.CM.SurfaceConstruction.realizeCoefficient_zero, map_zero]
    exact surface_algebraic E hScalarDescent hDegreeTwo hFunctoriality hThomClass hProjectionFormula H h R
      S.surface.variety X S.surface.property hX f π τ hsource
  · exact Elementary.CM.SurfaceConstruction.elementary_normalized_algebraic E hScalarDescent hDegreeTwo hThomClass hProjectionFormula v hid hother R X π

end

open _root_.CategoryTheory.Limits

/-- SurfaceConstruction: the four-factor switch tensor is nonzero and is represented
by an algebraic cycle with coefficients in the Galois CM field E. -/
theorem algebraic_cycle_realizing_switch
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : SurfaceConstructionOne.CM.DegreeTwoAlgebraicityInput)
    (hChernClass : SurfaceConstructionOne.CM.LefschetzOneOneInput)
    (hThetaCycle : Surface.CM.Construction.BallSurfaceSwitchInput E) (hFunctoriality : SurfaceConstructionQ.CM.ProperCycleClassCompatibility)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (v : Fin 4 →
      ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hswitch : ∀ τ : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val τ) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val τ) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val τ))
    (R : ∀ i : Fin 4,
      ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : ∀ i : Fin 4, X.toOver ⟶ (R i).abelianVariety.toOver)
    (hproduct : IsLimit (Fan.mk X.toOver π)) :
    let u : Fin 4 → Gal(E/ℚ) → X.complexCohomology 1 :=
      fun i τ =>
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
          ((R i).complexComparison
            (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
              (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)))
    let c := ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
    let t : X.complexCohomology 4 :=
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
        (Betti.Scheme.schemePointSpace X.toOver) 2 2
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 0 1) (u 1 1))
        (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ)
          (Betti.Scheme.schemePointSpace X.toOver) 1 1 (u 2 c) (u 3 c))
    t ≠ 0 ∧
      ∃ (n : ℕ) (a : Fin n → E)
        (Z : Fin n → CycleClass.Geometric.DimensionCycles.RationalDimensionCycle X 2),
        (∑ j : Fin n,
          (a j : ℂ) •
            X.rationalCohomologyInclusion 4
              (X.geometricCycleClassMap 2 (Z j))) = t := by
  dsimp only
  have ht := FourProduct.CM.SurfaceConstruction.canonical_switchTensor_ne_zero E v R X π hproduct
  refine ⟨ht, ?_⟩
  let : PathConnectedSpace X.analyticSpace :=
    Connected.CM.SurfaceConstruction.fourAbelianProduct_pathConnected (fun i => (R i).abelianVariety) X π hproduct
  have hX : 2 ≤ X.complexDimension := by
    have hd := Kunneth.CM.SurfaceConstruction.complex_degree_le X 4 _ ht
    omega
  obtain ⟨b, hb, hreal⟩ := Normalize.CM.SurfaceConstruction.switch_algebraic_of_normalized E
    (normalizedSwitchAlgebraicity_of_inputs E hScalarDescent
      (SurfaceConstructionOne.CM.degreeTwoAlgebraicity_of_inputs hDegreeTwo hChernClass) hThetaCycle hFunctoriality hThomClass hProjectionFormula)
    v hswitch R X hX π
  obtain ⟨n, a, Z, hz⟩ := Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses_finite_sum E X 2 hb
  exact ⟨n, a, Z, hz.trans hreal⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.SurfaceConstructionNe.CM
