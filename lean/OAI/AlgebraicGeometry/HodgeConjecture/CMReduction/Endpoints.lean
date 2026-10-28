import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.PairProducts
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.OppositePairs
import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CupPullback

/-! # Endpoints -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Endpoints.CM.Construction

noncomputable section

section

/-! Endpoint tensors on actual abelian varieties. Reflexivity is proved
by the finite product of the algebraic opposite-line divisor classes. -/

open _root_.CategoryTheory

variable (E : IntermediateField ℚ ℂ)
  [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]

def realizedVector {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (τ : Gal(E/ℚ)) :
    R.abelianVariety.variety.complexCohomology 1 :=
  R.complexComparison (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ))

def endpointClass (p : ℕ) (v w : Fin p → Pairing.CM.Construction.SignType E)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (g : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver) :
    X.variety.complexCohomology (p + p) :=
  IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) (p + p)
    (Fin.append
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i) (realizedVector E (R i) 1))
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
        (realizedVector E (T i) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))))

def EndpointAlgebraicity (p : ℕ) (v w : Fin p → Pairing.CM.Construction.SignType E) : Prop :=
  ∀ (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (f : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (g : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver),
    endpointClass E p v w R T X f g ∈ X.variety.complexGeometricAlgebraicClasses p

theorem endpointAlgebraicity_refl
    (h_ScalarDescent : Descent.CM.Construction.ScalarDescentInput) (hlefschetz : ComplexMultiplication.CMKnownResults.CM.KnownResults.LefschetzOneOne)
    (hexterior : ComplexMultiplication.KnownExteriorCohomology.CM.KnownResults.AbelianExteriorCohomology)
    (h_LineBundleCycles : CycleOperations.CM.Construction.LineBundleCyclesInput) (h_ThomClass : CycleOperations.CM.Construction.ExteriorInput)
    (p : ℕ) (v : Fin p → Pairing.CM.Construction.SignType E) : EndpointAlgebraicity E p v v := by
  intro R T X f g
  apply PairProducts.CM.Construction.h1Cup_of_algebraic_pairs hexterior h_LineBundleCycles h_ThomClass X p
  intro i
  have hc : ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) =
      ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) := by
    simpa only [mul_one] using ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation E 1
  unfold realizedVector
  rw [hc]
  exact OppositePairs.CM.Construction.canonical_opposite_pair_algebraic h_ScalarDescent hlefschetz E
    (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure_rankOneCMAction E (v i)) (R i) (T i) X.variety
    (f i) (g i) (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)

end

/-! Reuse the prescribed endpoint realization at every unchanged slot.
Retyping changes only the Hodge-structure proof, keeping its abelian variety
and rational marking definitionally fixed. -/

open _root_.CategoryTheory

def retypeRealization {U : Type} [AddCommGroup U] [Module ℚ U]
    {H J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (h : H = J) : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J where
  abelianVariety := R.abelianVariety
  comparison := R.comparison
  holomorphic x := by subst J; exact R.holomorphic x
  antiholomorphic x := by subst J; exact R.antiholomorphic x

theorem realizedVector_retype (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
    {H J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H) (h : H = J) (τ : Gal(E/ℚ)) :
    realizedVector E (retypeRealization R h) τ = realizedVector E R τ := rfl

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {p : ℕ} (w z : Fin p → Pairing.CM.Construction.SignType E) (a b : Fin p)
  (hrest : ∀ i, i ≠ a → i ≠ b → z i = w i)
  (T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (z i)))
  (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w a)))
  (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w b)))

def changedData (W X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : W.toOver ⟶ X.toOver)
    (g : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver)
    (f₁ : W.toOver ⟶ R₁.abelianVariety.toOver) (f₂ : W.toOver ⟶ R₂.abelianVariety.toOver)
    (i : Fin p) : Σ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w i)),
      W.toOver ⟶ R.abelianVariety.toOver :=
  if hia : i = a then ⟨retypeRealization R₁ (by subst i; rfl), f₁⟩
  else if hib : i = b then ⟨retypeRealization R₂ (by subst i; rfl), f₂⟩
  else ⟨retypeRealization (T i) (congrArg (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E) (hrest i hia hib)), f ≫ g i⟩

def realizedMapValue {H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure E} (W : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (d : Σ R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization H, W.toOver ⟶ R.abelianVariety.toOver) (τ : Gal(E/ℚ)) :
    W.variety.complexCohomology 1 :=
  Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 d.2 (realizedVector E d.1 τ)

theorem changed_pullback (W X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : W.toOver ⟶ X.toOver)
    (g : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver)
    (f₁ : W.toOver ⟶ R₁.abelianVariety.toOver) (f₂ : W.toOver ⟶ R₂.abelianVariety.toOver)
    (i : Fin p) (τ : Gal(E/ℚ)) :
    realizedMapValue E W (changedData E w z a b hrest T R₁ R₂ W X f g f₁ f₂ i) τ =
    if i = a then Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f₁ (realizedVector E R₁ τ)
    else if i = b then Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f₂ (realizedVector E R₂ τ)
    else Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i) (realizedVector E (T i) τ)) := by
  by_cases hia : i = a
  · rw [changedData, dite_eq_left hia, ite_eq_left hia]
    rfl
  · by_cases hib : i = b
    · rw [changedData, dite_eq_right hia, dite_eq_left hib, ite_eq_right hia, ite_eq_left hib]
      rfl
    · rw [changedData, dite_eq_right hia, dite_eq_right hib, ite_eq_right hia, ite_eq_right hib]
      exact (CupPullback.CM.Construction.scheme_pullback_comp (R := ℂ) f (g i) 1 (realizedVector E (T i) τ)).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Endpoints.CM.Construction
