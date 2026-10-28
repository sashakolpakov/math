import OAI.AlgebraicGeometry.HodgeConjecture.NegRealization
import OAI.AlgebraicGeometry.HodgeConjecture.Elementary

/-! # Normalize -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.Normalize.CM.SurfaceConstruction

noncomputable section

/-! Exhaustive normalization of the six possible identity-sign patterns.
Negated types retain the actual abelian varieties with conjugated rational
markings. Only even cup permutations are used. -/

open _root_.CategoryTheory
open scoped TensorProduct

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

/-- The normalized statement used only as a proved intermediate reduction. -/
def NormalizedSwitchAlgebraicity : Prop :=
  ∀ (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (_hbalance : ∀ g : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val g) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val g))
    (_hid : ∀ i, (v i).val 1 = true)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) [PathConnectedSpace X.analyticSpace]
    (_hX : 2 ≤ X.complexDimension)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver),
    ∃ a : E ⊗[ℚ] X.rationalCohomology 4,
      a ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 ∧
      Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 4 a = SurfaceConstructionQ.CM.fourCup X (fun i =>
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
          ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
            (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
              (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))))

theorem switch_algebraic_of_normalized (hN : NormalizedSwitchAlgebraicity E)
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g))
    (hbalance : ∀ g : Gal(E/ℚ),
      ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val g) =
        ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val g))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) [PathConnectedSpace X.analyticSpace]
    (hX : 2 ≤ X.complexDimension)
    (π : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) :
    ∃ a : E ⊗[ℚ] X.rationalCohomology 4,
      a ∈ Coefficients.CM.SurfaceConstruction.coefficientAlgebraicClasses E X 2 ∧
      Coefficients.CM.SurfaceConstruction.realizeCoefficient E X 4 a = SurfaceConstructionQ.CM.fourCup X (fun i =>
        Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
          ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
            (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
              (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) := by
  let u : Fin 4 → X.complexCohomology 1 := fun i =>
    Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π i)
      ((R i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
        (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
          (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))
  have hb1 := hbalance 1
  cases h0 : (v 0).val 1 <;> cases h1 : (v 1).val 1 <;>
    cases h2 : (v 2).val 1 <;> cases h3 : (v 3).val 1 <;>
    try (norm_num [ComplexMultiplication.SignSwitch.CM.signValue, h0, h1, h2, h3] at hb1)
  · let w : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g) := ![(v 2).neg, (v 3).neg, (v 0).neg, (v 1).neg]
    let T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)) :=
      (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 2) (R 2)) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 3) (R 3)) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 0) (R 0)) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 1) (R 1)) (fun i => i.elim0)))))
    let ρ : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver :=
      (Fin.cons (π 2) (Fin.cons (π 3) (Fin.cons (π 0) (Fin.cons (π 1) (fun i => i.elim0)))))
    have hwid : ∀ i, (w i).val 1 = true := by
      intro i
      fin_cases i <;> norm_num [w, h0, h1, h2, h3]
    have hwbal : ∀ g : Gal(E/ℚ),
        ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val g) =
          ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val g) := by
      intro g
      have hb := hbalance g
      change ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 2).val g)) + ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 3).val g)) = ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 0).val g)) + ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 1).val g))
      simp only [ComplexMultiplication.SignSwitch.CM.signValue_not]
      linarith
    obtain ⟨a, ha, har⟩ := hN w hwbal hwid T X hX ρ
    refine ⟨a, ha, har.trans ?_⟩
    have he : (fun i : Fin 4 => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (ρ i)
        ((T i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) =
        ![u 2, u 3, u 0, u 1] := by
      funext i
      fin_cases i
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 2))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_one E (v 2) (R 2))
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 3))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_one E (v 3) (R 3))
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 0))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v 0) (R 0))
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 1))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v 1) (R 1))
    refine (congrArg (SurfaceConstructionQ.CM.fourCup X) he).trans ?_
    exact CupRegrouping.CM.SurfaceConstruction.cup22_comm (Betti.Scheme.schemePointSpace X.toOver) _ _
  · let w : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g) := ![v 1, (v 2).neg, (v 0).neg, v 3]
    let T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)) :=
      (Fin.cons (R 1) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 2) (R 2)) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 0) (R 0)) (Fin.cons (R 3) (fun i => i.elim0)))))
    let ρ : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver :=
      (Fin.cons (π 1) (Fin.cons (π 2) (Fin.cons (π 0) (Fin.cons (π 3) (fun i => i.elim0)))))
    have hwid : ∀ i, (w i).val 1 = true := by
      intro i
      fin_cases i <;> norm_num [w, h0, h1, h2, h3]
    have hwbal : ∀ g : Gal(E/ℚ),
        ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val g) =
          ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val g) := by
      intro g
      have hb := hbalance g
      change ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val g) + ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 2).val g)) = ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 0).val g)) + ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val g)
      simp only [ComplexMultiplication.SignSwitch.CM.signValue_not]
      linarith
    obtain ⟨a, ha, har⟩ := hN w hwbal hwid T X hX ρ
    refine ⟨a, ha, har.trans ?_⟩
    have he : (fun i : Fin 4 => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (ρ i)
        ((T i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) =
        ![u 1, u 2, u 0, u 3] := by
      funext i
      fin_cases i
      · rfl
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 2))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_one E (v 2) (R 2))
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 0))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v 0) (R 0))
      · rfl
    refine (congrArg (SurfaceConstructionQ.CM.fourCup X) he).trans ?_
    exact (CupRegrouping.CM.SurfaceConstruction.cup22_comm (Betti.Scheme.schemePointSpace X.toOver) _ _).trans
      (CupRegrouping.CM.SurfaceConstruction.cup1111_cycle_twice (Betti.Scheme.schemePointSpace X.toOver) (u 0) (u 1) (u 2) (u 3)).symm
  · let w : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g) := ![(v 3).neg, v 1, (v 0).neg, v 2]
    let T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)) :=
      (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 3) (R 3)) (Fin.cons (R 1) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 0) (R 0)) (Fin.cons (R 2) (fun i => i.elim0)))))
    let ρ : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver :=
      (Fin.cons (π 3) (Fin.cons (π 1) (Fin.cons (π 0) (Fin.cons (π 2) (fun i => i.elim0)))))
    have hwid : ∀ i, (w i).val 1 = true := by
      intro i
      fin_cases i <;> norm_num [w, h0, h1, h2, h3]
    have hwbal : ∀ g : Gal(E/ℚ),
        ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val g) =
          ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val g) := by
      intro g
      have hb := hbalance g
      change ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 3).val g)) + ComplexMultiplication.SignSwitch.CM.signValue ((v 1).val g) = ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 0).val g)) + ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val g)
      simp only [ComplexMultiplication.SignSwitch.CM.signValue_not]
      linarith
    obtain ⟨a, ha, har⟩ := hN w hwbal hwid T X hX ρ
    refine ⟨a, ha, har.trans ?_⟩
    have he : (fun i : Fin 4 => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (ρ i)
        ((T i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) =
        ![u 3, u 1, u 0, u 2] := by
      funext i
      fin_cases i
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 3))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_one E (v 3) (R 3))
      · rfl
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 0))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v 0) (R 0))
      · rfl
    refine (congrArg (SurfaceConstructionQ.CM.fourCup X) he).trans ?_
    exact (CupRegrouping.CM.SurfaceConstruction.cup22_comm (Betti.Scheme.schemePointSpace X.toOver) _ _).trans
      (CupRegrouping.CM.SurfaceConstruction.cup1111_cycle (Betti.Scheme.schemePointSpace X.toOver) (u 0) (u 1) (u 2) (u 3)).symm
  · let w : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g) := ![v 0, (v 2).neg, v 3, (v 1).neg]
    let T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)) :=
      (Fin.cons (R 0) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 2) (R 2)) (Fin.cons (R 3) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 1) (R 1)) (fun i => i.elim0)))))
    let ρ : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver :=
      (Fin.cons (π 0) (Fin.cons (π 2) (Fin.cons (π 3) (Fin.cons (π 1) (fun i => i.elim0)))))
    have hwid : ∀ i, (w i).val 1 = true := by
      intro i
      fin_cases i <;> norm_num [w, h0, h1, h2, h3]
    have hwbal : ∀ g : Gal(E/ℚ),
        ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val g) =
          ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val g) := by
      intro g
      have hb := hbalance g
      change ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 2).val g)) = ComplexMultiplication.SignSwitch.CM.signValue ((v 3).val g) + ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 1).val g))
      simp only [ComplexMultiplication.SignSwitch.CM.signValue_not]
      linarith
    obtain ⟨a, ha, har⟩ := hN w hwbal hwid T X hX ρ
    refine ⟨a, ha, har.trans ?_⟩
    have he : (fun i : Fin 4 => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (ρ i)
        ((T i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) =
        ![u 0, u 2, u 3, u 1] := by
      funext i
      fin_cases i
      · rfl
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 2))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_one E (v 2) (R 2))
      · rfl
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 1))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v 1) (R 1))
    refine (congrArg (SurfaceConstructionQ.CM.fourCup X) he).trans ?_
    exact (CupRegrouping.CM.SurfaceConstruction.cup1111_cycle (Betti.Scheme.schemePointSpace X.toOver) (u 0) (u 1) (u 2) (u 3)).symm
  · let w : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
        (fun g : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * g) := ![v 0, (v 3).neg, (v 1).neg, v 2]
    let T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)) :=
      (Fin.cons (R 0) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 3) (R 3)) (Fin.cons (NegRealization.CM.SurfaceConstruction.negRealization E (v 1) (R 1)) (Fin.cons (R 2) (fun i => i.elim0)))))
    let ρ : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver :=
      (Fin.cons (π 0) (Fin.cons (π 3) (Fin.cons (π 1) (Fin.cons (π 2) (fun i => i.elim0)))))
    have hwid : ∀ i, (w i).val 1 = true := by
      intro i
      fin_cases i <;> norm_num [w, h0, h1, h2, h3]
    have hwbal : ∀ g : Gal(E/ℚ),
        ComplexMultiplication.SignSwitch.CM.signValue ((w 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 1).val g) =
          ComplexMultiplication.SignSwitch.CM.signValue ((w 2).val g) + ComplexMultiplication.SignSwitch.CM.signValue ((w 3).val g) := by
      intro g
      have hb := hbalance g
      change ComplexMultiplication.SignSwitch.CM.signValue ((v 0).val g) + ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 3).val g)) = ComplexMultiplication.SignSwitch.CM.signValue (Bool.not ((v 1).val g)) + ComplexMultiplication.SignSwitch.CM.signValue ((v 2).val g)
      simp only [ComplexMultiplication.SignSwitch.CM.signValue_not]
      linarith
    obtain ⟨a, ha, har⟩ := hN w hwbal hwid T X hX ρ
    refine ⟨a, ha, har.trans ?_⟩
    have he : (fun i : Fin 4 => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (ρ i)
        ((T i).complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E
            (if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))) =
        ![u 0, u 3, u 1, u 2] := by
      funext i
      fin_cases i
      · rfl
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 3))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_one E (v 3) (R 3))
      · exact congrArg (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (π 1))
          (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v 1) (R 1))
      · rfl
    refine (congrArg (SurfaceConstructionQ.CM.fourCup X) he).trans ?_
    exact (CupRegrouping.CM.SurfaceConstruction.cup1111_cycle_twice (Betti.Scheme.schemePointSpace X.toOver) (u 0) (u 1) (u 2) (u 3)).symm
  · exact hN v hbalance (by intro i; fin_cases i <;> assumption) R X hX π

end

end OAI.AlgebraicGeometry.HodgeConjecture.Normalize.CM.SurfaceConstruction
