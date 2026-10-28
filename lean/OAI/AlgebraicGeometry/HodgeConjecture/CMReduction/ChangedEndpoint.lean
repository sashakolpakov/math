import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Endpoints

/-! # Changed Endpoint -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ChangedEndpoint.CM.Construction

noncomputable section

section

/-! The literal endpoint tuple obtained by replacing the two active
realizations. The remaining entries are all pullbacks of the target tuple. -/

open _root_.CategoryTheory

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
  {p : ℕ} (w z : Fin p → Pairing.CM.Construction.SignType E) (a b : Fin p)
  (hrest : ∀ i, i ≠ a → i ≠ b → z i = w i)
  (T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (z i)))
  (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w a)))
  (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w b)))
  (W X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : W.toOver ⟶ X.toOver)
  (g : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver)
  (f₁ : W.toOver ⟶ R₁.abelianVariety.toOver) (f₂ : W.toOver ⟶ R₂.abelianVariety.toOver)
  (s : Fin p → X.variety.complexCohomology 1)

def changedTuple : Fin (p + p) → W.variety.complexCohomology 1 :=
  Fin.append (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (s i))
    (fun i => Endpoints.CM.Construction.realizedMapValue E W (Endpoints.CM.Construction.changedData E w z a b hrest T R₁ R₂ W X f g f₁ f₂ i)
      (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))

def targetTuple : Fin (p + p) → X.variety.complexCohomology 1 :=
  Fin.append s (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i)
    (Endpoints.CM.Construction.realizedVector E (T i) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)))

theorem changedTuple_rest (i : Fin (p + p))
    (hia : i ≠ Fin.natAdd p a) (hib : i ≠ Fin.natAdd p b) :
    changedTuple E w z a b hrest T R₁ R₂ W X f g f₁ f₂ s i =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f (targetTuple E z T X g s i) := by
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin p ≃ Fin (p + p)).surjective i
  cases j with
  | inl j =>
    rw [changedTuple, targetTuple, finSumFinEquiv_apply_left, Fin.append_left, Fin.append_left]
  | inr j =>
    have hja : j ≠ a := fun h => hia (congrArg (Fin.natAdd p) h)
    have hjb : j ≠ b := fun h => hib (congrArg (Fin.natAdd p) h)
    rw [changedTuple, targetTuple, finSumFinEquiv_apply_right, Fin.append_right, Fin.append_right]
    rw [Endpoints.CM.Construction.changed_pullback, ite_eq_right hja, ite_eq_right hjb]

theorem changedTuple_first :
    changedTuple E w z a b hrest T R₁ R₂ W X f g f₁ f₂ s (Fin.natAdd p a) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f₁ (Endpoints.CM.Construction.realizedVector E R₁ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
  rw [changedTuple, Fin.append_right]
  rw [Endpoints.CM.Construction.changed_pullback, ite_eq_left rfl]

theorem changedTuple_second (hab : a ≠ b) :
    changedTuple E w z a b hrest T R₁ R₂ W X f g f₁ f₂ s (Fin.natAdd p b) =
      Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 f₂ (Endpoints.CM.Construction.realizedVector E R₂ (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E)) := by
  rw [changedTuple, Fin.append_right]
  rw [Endpoints.CM.Construction.changed_pullback, ite_eq_right hab.symm, ite_eq_left rfl]

end

open _root_.CategoryTheory

theorem endpointClass_changed
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    {p : ℕ} (v w z : Fin p → Pairing.CM.Construction.SignType E) (a b : Fin p)
    (hrest : ∀ i, i ≠ a → i ≠ b → z i = w i)
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (T : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (z i)))
    (R₁ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w a)))
    (R₂ : ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (w b)))
    (W X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (f : W.toOver ⟶ X.toOver)
    (s : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver)
    (g : ∀ i, X.toOver ⟶ (T i).abelianVariety.toOver)
    (f₁ : W.toOver ⟶ R₁.abelianVariety.toOver) (f₂ : W.toOver ⟶ R₂.abelianVariety.toOver) :
    Endpoints.CM.Construction.endpointClass E p v w R
      (fun i => (Endpoints.CM.Construction.changedData E w z a b hrest T R₁ R₂ W X f g f₁ f₂ i).1)
      W (fun i => f ≫ s i)
      (fun i => (Endpoints.CM.Construction.changedData E w z a b hrest T R₁ R₂ W X f g f₁ f₂ i).2) =
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace W.toOver) (p + p)
      (changedTuple E w z a b hrest T R₁ R₂ W X f g f₁ f₂
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (s i) (Endpoints.CM.Construction.realizedVector E (R i) 1))) := by
  unfold Endpoints.CM.Construction.endpointClass changedTuple
  apply congrArg (IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace W.toOver) (p + p))
  funext i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin p ≃ Fin (p + p)).surjective i
  cases j with
  | inl j =>
    rw [finSumFinEquiv_apply_left, Fin.append_left, Fin.append_left]
    exact (CupPullback.CM.Construction.scheme_pullback_comp (R := ℂ) f (s j) 1 (Endpoints.CM.Construction.realizedVector E (R j) 1)).symm
  | inr j =>
    rw [finSumFinEquiv_apply_right, Fin.append_right, Fin.append_right]
    rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.ChangedEndpoint.CM.Construction
