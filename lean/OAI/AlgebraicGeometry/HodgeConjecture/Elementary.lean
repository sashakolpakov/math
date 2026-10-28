import OAI.AlgebraicGeometry.HodgeConjecture.CanonicalCoefficients

/-! # Elementary -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Elementary.CM.SurfaceConstruction

noncomputable section

/-! The elementary case when the Galois group has only the identity and
complex conjugation. Normalized odd types then agree, and two divisor pairs
give the desired codimension-two class. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

omit [IsGalois ℚ E] in
theorem normalized_type_eq
    (v w : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (hv : v.val 1 = true) (hw : w.val 1 = true)
    (hother : ¬ ∃ τ : Gal(E/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) : v = w := by
  apply Subtype.ext
  funext g
  by_cases h1 : g = 1
  · simp only [h1, hv, hw]
  by_cases hc : g = ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E
  · have hvc := v.property 1
    have hwc := w.property 1
    simp only [mul_one, hv] at hvc
    simp only [mul_one, hw] at hwc
    simpa only [hc] using hvc.trans hwc.symm
  exact False.elim (hother ⟨g, h1, hc⟩)

theorem pair_of_equal_HodgeStructures
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (H J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E) (h : ComplexMultiplication.WeightOne.CM.RankOneCMAction E H) (hHJ : H = J)
    (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (T : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J)
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : X.toOver ⟶ R.abelianVariety.toOver) (g : X.toOver ⟶ T.abelianVariety.toOver)
    (τ : E →ₐ[ℚ] ℂ) :
    ∃ a : E ⊗[ℚ] X.rationalCohomology 2, a ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 1 ∧
      Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 2 a = AlgebraicTopology.Products.CupCohomology.singularCohomologyCup (R := ℂ) (Betti.Scheme.schemePointSpace X.toOver) 1 1
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E τ)))
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 g
          (T.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ)))) := by
  subst J
  exact ⟨Pairs.CM.SurfaceConstruction.normalizedOppositePair E h R T X f g τ,
    Pairs.CM.SurfaceConstruction.normalizedOppositePair_algebraic E hScalarDescent hDegreeTwo h R T X f g τ,
    Pairs.CM.SurfaceConstruction.normalizedOppositePair_realize E h R T X f g τ⟩

theorem elementary_normalized_algebraic
    (hScalarDescent : Coefficients.CM.SurfaceConstruction.ScalarTraceDescent E) (hDegreeTwo : Coefficients.CM.SurfaceConstruction.DegreeTwoAlgebraicity)
    (hThomClass : Intersections.CM.SurfaceConstruction.IntersectionCycleClassCompatibility) (hProjectionFormula : Intersections.CM.SurfaceConstruction.ChowProjectionFormula)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (hid : ∀ i, (v i).val 1 = true)
    (hother : ¬ ∃ τ : Gal(E/ℚ), τ ≠ 1 ∧ τ ≠ ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) :
    CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E
      (fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i))
      (fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E (v i)) R X π
      (fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
        (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) ∈
      Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 := by
  let H := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)
  let h := fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E (v i)
  let τ := ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1
  have heq (i j : Fin 4) : H i = H j := congrArg (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E)
    (normalized_type_eq E (v i) (v j) (hid i) (hid j) hother)
  obtain ⟨a, ha, har⟩ := pair_of_equal_HodgeStructures E hScalarDescent hDegreeTwo
    (H 0) (H 2) (h 0) (heq 0 2) (R 0) (R 2) X (π 0) (π 2) τ
  obtain ⟨b, hb, hbr⟩ := pair_of_equal_HodgeStructures E hScalarDescent hDegreeTwo
    (H 1) (H 3) (h 1) (heq 1 3) (R 1) (R 3) X (π 1) (π 3) τ
  have hab := Products.CM.SurfaceConstruction.coefficientCup_algebraic E hThomClass hProjectionFormula X 1 1 a b ha hb
  change CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 2 2 a b ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 at hab
  have halg := (Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2).smul_mem (-1 : E) hab
  have hconj : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding τ =
      ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) := by
    simpa only [mul_one] using (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E 1).symm
  have hc : (-1 : E) • CoefficientCups.CM.SurfaceConstruction.coefficientCup E X 2 2 a b =
      CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient E H h R X π (fun i => ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
        (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
    apply CanonicalCoefficients.CM.SurfaceConstruction.realizeCoefficient_injective E X 4
    rw [Pairs.CM.SurfaceConstruction.realizeCoefficient_smul]
    erw [CoefficientCups.CM.SurfaceConstruction.realizeCoefficient_cup E X 2 2]
    rw [har, hbr, CanonicalCoefficients.CM.SurfaceConstruction.canonicalFourCoefficient_realize]
    simp only [hconj, IntermediateField.coe_neg, IntermediateField.coe_one, neg_one_smul, SurfaceConstructionQ.CM.fourCup]
    exact (CupRegrouping.CM.SurfaceConstruction.cup1111_exchange (Betti.Scheme.schemePointSpace X.toOver) _ _ _ _).symm
  exact hc ▸ halg

end

end OAI.AlgebraicGeometry.HodgeConjecture.Elementary.CM.SurfaceConstruction
