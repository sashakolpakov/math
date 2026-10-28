import OAI.AlgebraicGeometry.HodgeConjecture.Coefficients
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.LineTransfer
import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.RationalCup
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity
import OAI.AlgebraicTopology.DeRham.Comparison.ProjectiveHodgeNaturality
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! # Pairs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Pairs.CM.SurfaceConstruction

noncomputable section

/-!
Actual opposite-embedding pair classes on two independently supplied abelian
realizations of the same CM Hodge structure. Pair algebraicity follows from
the full scalar-trace and degree-two hypotheses; it is not an input field.
The variety P carries two algebraic maps to the realizations, so this also
applies to the pair projections in a product with additional factors.
-/

open _root_.CategoryTheory
open scoped TensorProduct

@[simp]
theorem realizeCoefficient_zero (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n 0 = 0 := by
  simp [Coefficients.CM.SurfaceConstruction.realizeCoefficient]

@[simp]
theorem realizeCoefficient_add (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (x y : E ⊗[ℚ] X.rationalCohomology n) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n (x + y) =
      Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n x + Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n y := by
  simp [Coefficients.CM.SurfaceConstruction.realizeCoefficient]

theorem realizeCoefficient_smul (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ)
    (a : E) (x : E ⊗[ℚ] X.rationalCohomology n) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n (a • x) = (a : ℂ) • Coefficients.CM.SurfaceConstruction.realizeCoefficient E X n x := by
  simp [Coefficients.CM.SurfaceConstruction.realizeCoefficient, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_smul]

/-- The coefficient extension of the actual rational H1 cup product. -/
def coefficientH1Cup (E : IntermediateField ℚ ℂ) (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    (E ⊗[ℚ] X.rationalCohomology 1) →ₗ[E]
      (E ⊗[ℚ] X.rationalCohomology 1) →ₗ[E]
        (E ⊗[ℚ] X.rationalCohomology 2) :=
  LinearMap.BilinMap.baseChange E
    (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 1 1)

theorem coefficientH1Cup_conjugate (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (σ : Gal(E/ℚ))
    (u v : E ⊗[ℚ] X.rationalCohomology 1) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 2) σ (coefficientH1Cup E X u v) =
      coefficientH1Cup E X
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 1) σ u)
        (ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (X.rationalCohomology 1) σ v) := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp [hu, hw]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp [hv, hw]
    | tmul b y => simp [coefficientH1Cup, LinearMap.BilinMap.baseChange_tmul]

/-- Coefficient extension agrees with the native complex cup operation. -/
theorem realizeCoefficient_h1Cup (E : IntermediateField ℚ ℂ)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u v : E ⊗[ℚ] X.rationalCohomology 1) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 2 (coefficientH1Cup E X u v) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1
        (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 1 u) (Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 1 v) := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp [hu, hw]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp [hv, hw]
    | tmul b y =>
      simp only [coefficientH1Cup, LinearMap.BilinMap.baseChange_tmul,
        Coefficients.CM.SurfaceConstruction.realizeCoefficient_tmul, IntermediateField.coe_mul]
      change ((a : ℂ) * (b : ℂ)) •
        AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) 2
          (AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℚ) (Betti.Scheme.schemePointSpace X.toOver) 1 1 x y) =
        AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1
          ((a : ℂ) • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) 1 x)
          ((b : ℂ) • AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace X.toOver) 1 y)
      erw [map_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul, mul_comm (b : ℂ) (a : ℂ)]
      exact congrArg (fun z => ((a : ℂ) * (b : ℂ)) • z)
        (ComplexMultiplication.HodgeComparison.RationalCup.CM.Construction.rationalToComplexCohomology_cup (Betti.Scheme.schemePointSpace X.toOver) 1 1 x y)

/-- Canonical complexification commutes with algebraic pullback. -/
theorem complexification_pullback {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (f : X.toOver ⟶ Y.toOver) (n : ℕ)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology n)) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) n
      ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) n f).hom.baseChange ℂ x) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) n x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [hx, hy]
  | tmul a x =>
    simp only [LinearMap.baseChange_tmul, ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification_tmul]
    calc
      _ = a • Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f
          (AlgebraicTopology.Cohomology.Singular.RationalComplex.rationalToComplexCohomology (Betti.Scheme.schemePointSpace Y.toOver) n x) :=
        congrArg (fun z => a • z)
          (ConcreteCategory.congr_hom (Betti.Scheme.schemeBettiRationalInclusion_naturality f n) x)
      _ = _ := ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) n f).hom.map_smul a _).symm

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
variable {U : Type} [AddCommGroup U] [Module ℚ U] [Module E U]
  [IsScalarTower ℚ E U] {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U}

/-- A realized embedding generator, pulled to the actual product over E. -/
def pulledEmbeddingCoefficient (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : P.toOver ⟶ R.abelianVariety.toOver)
    (τ : E →ₐ[ℚ] ℂ) : E ⊗[ℚ] P.rationalCohomology 1 :=
  (((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 π).hom.comp R.comparison.toLinearMap).baseChange E)
    (h.coefficientEmbeddingBasis E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) τ)

omit [NumberField.IsCMField E] in
theorem pulledEmbeddingCoefficient_realize (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : P.toOver ⟶ R.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E P 1 (pulledEmbeddingCoefficient E h R P π τ) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 π
        (R.complexComparison (h.embeddingBasis τ)) := by
  unfold Coefficients.CM.SurfaceConstruction.realizeCoefficient pulledEmbeddingCoefficient
  rw [ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion_baseChange, h.coefficientInclusion_embeddingBasis,
    LinearMap.baseChange_comp, LinearMap.comp_apply, complexification_pullback]
  rfl

omit [NumberField.IsCMField E] in
theorem pulledEmbeddingCoefficient_conjugate (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : P.toOver ⟶ R.abelianVariety.toOver)
    (σ : Gal(E/ℚ)) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (P.rationalCohomology 1) σ
      (pulledEmbeddingCoefficient E h R P π τ) =
      pulledEmbeddingCoefficient E h R P π
        (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ τ) := by
  unfold pulledEmbeddingCoefficient
  rw [ComplexMultiplication.EmbeddingCoefficientField.CM.scalarConjugate_baseChange, h.scalarConjugate_coefficientEmbeddingBasis]

theorem galoisCoefficientEmbedding_opposite (σ : Gal(E/ℚ)) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) =
      ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding
        (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ τ) := by
  ext x
  have hc : ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) x =
      ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) τ
        (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E x) := by
    apply Subtype.ext
    exact (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E τ.toRingHom x).symm
  change (σ (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) x) : ℂ) = _
  rw [hc]
  exact ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E
    (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ τ).toRingHom x

/-- The pair class uses opposite labels on independent realizations. -/
def oppositePair (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    E ⊗[ℚ] P.rationalCohomology 2 :=
  coefficientH1Cup E P (pulledEmbeddingCoefficient E h R P πR τ)
    (pulledEmbeddingCoefficient E h T P πT (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ))

theorem oppositePair_conjugate (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver)
    (σ : Gal(E/ℚ)) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ E (P.rationalCohomology 2) σ (oppositePair E h R T P πR πT τ) =
      oppositePair E h R T P πR πT
        (ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) σ τ) := by
  unfold oppositePair
  rw [coefficientH1Cup_conjugate, pulledEmbeddingCoefficient_conjugate,
    pulledEmbeddingCoefficient_conjugate, galoisCoefficientEmbedding_opposite]

omit [NumberField.IsCMField E] in
/-- Each pair is of type (1,1), regardless of the sign at the selected embedding. -/
theorem oppositePair_hodge (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E P 2 (oppositePair E h R T P πR πT τ) ∈
      P.pureBettiSubspace 1 1 := by
  unfold oppositePair
  rw [realizeCoefficient_h1Cup, pulledEmbeddingCoefficient_realize,
    pulledEmbeddingCoefficient_realize]
  by_cases hs : h.embeddingSign τ = true
  · have hR := (R.complexComparison_holomorphic (h.embeddingBasis τ)).mpr
      ((h.embeddingBasis_mem_holomorphic_iff τ).mpr hs)
    have hT := (T.complexComparison_antiholomorphic
      (h.embeddingBasis (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ))).mpr
      ((h.embeddingBasis_mem_antiholomorphic_iff _).mpr (by
        rw [h.embeddingSign_conjugate, hs]; rfl))
    have hRp := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace πR 1 0 hR
    have hTp := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace πT 0 1 hT
    exact AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveCup_mem_pure P 1 0 0 1 _ _ hRp hTp
  · have hs' : h.embeddingSign τ = false := Bool.eq_false_iff.mpr hs
    have hR := (R.complexComparison_antiholomorphic (h.embeddingBasis τ)).mpr
      ((h.embeddingBasis_mem_antiholomorphic_iff τ).mpr hs')
    have hT := (T.complexComparison_holomorphic
      (h.embeddingBasis (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ))).mpr
      ((h.embeddingBasis_mem_holomorphic_iff _).mpr (by
        rw [h.embeddingSign_conjugate, hs']; rfl))
    have hRp := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace πR 0 1 hR
    have hTp := Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexBettiPullback_mem_pureBettiSubspace πT 1 0 hT
    exact AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveCup_mem_pure P 0 1 1 0 _ _ hRp hTp

/-- The pair class is algebraic over E by full trace descent and Lefschetz. -/
theorem oppositePair_algebraic (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E)
    (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    oppositePair E h R T P πR πT τ ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E P 1 := by
  apply Coefficients.CM.SurfaceConstruction.degreeTwo_algebraic_of_conjugates E hScalarDescent hDegreeTwo
  intro σ
  rw [oppositePair_conjugate]
  exact oppositePair_hodge E h R T P πR πT _

omit [IsGalois ℚ E] [NumberField.IsCMField E] in
/-- Remove the rank-one basis normalization using a scalar in the acting
field. The result is the exact embeddingVector used by the SurfaceConstruction statement. -/
theorem field_embeddingVector_normalization {Hfield : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E}
    (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E Hfield) (τ : E →ₐ[ℚ] ℂ) :
    ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ = τ (h.equivField 1) • h.embeddingBasis τ := by
  have hm : (h.equivField.restrictScalars ℚ).toLinearMap =
      ComplexMultiplication.WeightOne.CM.scalarEndomorphism (U := E) E (h.equivField 1) := by
    apply LinearMap.ext
    intro x
    change h.equivField x = h.equivField 1 * x
    calc
      _ = x * h.equivField 1 := by
        simpa only [smul_eq_mul, mul_one] using h.equivField.map_smul x (1 : E)
      _ = _ := mul_comm _ _
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E).injective
  calc
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ) =
        h.complexEmbeddingEquiv (h.embeddingBasis τ) := by
      rw [ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector,
        h.complexEmbeddingEquiv_embeddingBasis]
    _ = ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E
        ((h.equivField.restrictScalars ℚ).toLinearMap.baseChange ℂ (h.embeddingBasis τ)) := rfl
    _ = ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E
        ((ComplexMultiplication.WeightOne.CM.scalarEndomorphism (U := E) E (h.equivField 1)).baseChange ℂ
          (h.embeddingBasis τ)) := by rw [hm]
    _ = _ := congrArg (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv E)
      (h.embeddingBasis_eigen (h.equivField 1) τ)

/-- The normalized pair uses only E coefficients and realizes exactly the
two canonical embedding vectors in the manuscript's field model. -/
def normalizedOppositePair {Hfield : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E}
    (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E Hfield) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Hfield)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    E ⊗[ℚ] P.rationalCohomology 2 :=
  (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E) τ (h.equivField 1) *
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding E E (ComplexMultiplication.CM.LineTransfer.CMCoefficientField.embedding_fieldRange_le E)
      (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ) (h.equivField 1)) • oppositePair E h R T P πR πT τ

omit [NumberField.IsCMField E] in
theorem normalizedOppositePair_realize {Hfield : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E}
    (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E Hfield) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Hfield)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    Coefficients.CM.SurfaceConstruction.realizeCoefficient E P 2 (normalizedOppositePair E h R T P πR πT τ) =
      AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace P.toOver) 1 1
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πR (R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ)))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 πT
          (T.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)))) := by
  rw [normalizedOppositePair, realizeCoefficient_smul, oppositePair,
    realizeCoefficient_h1Cup, pulledEmbeddingCoefficient_realize,
    pulledEmbeddingCoefficient_realize, IntermediateField.coe_mul,
    ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding_coe, ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding_coe,
    field_embeddingVector_normalization E h τ,
    field_embeddingVector_normalization E h (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)]
  simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm]

theorem normalizedOppositePair_algebraic (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E)
    (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity) {Hfield : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E}
    (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E Hfield) (R T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization Hfield)
    (P : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (πR : P.toOver ⟶ R.abelianVariety.toOver)
    (πT : P.toOver ⟶ T.abelianVariety.toOver) (τ : E →ₐ[ℚ] ℂ) :
    normalizedOppositePair E h R T P πR πT τ ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E P 1 :=
  (Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E P 1).smul_mem _
    (oppositePair_algebraic E hScalarDescent hDegreeTwo h R T P πR πT τ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.Pairs.CM.SurfaceConstruction
