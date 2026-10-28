import OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.Endpoints
import OAI.AlgebraicGeometry.HodgeConjecture.NegRealization

/-! # Canonical Tuple -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalTuple.CM.Construction

noncomputable section

/-! Interpret a balanced tuple as endpoint data by conjugating the
rational markings in its second half. The abelian varieties stay fixed. -/

open _root_.CategoryTheory

theorem canonical_tuple_of_endpoint
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (p : ℕ) (v : Fin (p + p) → Pairing.CM.Construction.SignType E)
    (hendpoint : Endpoints.CM.Construction.EndpointAlgebraicity E p
      (fun i => v (Fin.castAdd p i)) (fun i => (v (Fin.natAdd p i)).neg))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E (v i)))
    (X : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (g : ∀ i, X.toOver ⟶ (R i).abelianVariety.toOver) :
    IteratedCup.CM.Construction.h1Cup ℂ (Betti.Scheme.schemePointSpace X.toOver) (p + p)
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i) (Endpoints.CM.Construction.realizedVector E (R i) 1)) ∈
      X.variety.complexGeometricAlgebraicClasses p := by
  have h := hendpoint (fun i => R (Fin.castAdd p i))
    (fun i => NegRealization.CM.SurfaceConstruction.negRealization E (v (Fin.natAdd p i)) (R (Fin.natAdd p i)))
    X (fun i => g (Fin.castAdd p i)) (fun i => g (Fin.natAdd p i))
  unfold Endpoints.CM.Construction.endpointClass at h
  have heq :
      Fin.append
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g (Fin.castAdd p i))
          (Endpoints.CM.Construction.realizedVector E (R (Fin.castAdd p i)) 1))
        (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g (Fin.natAdd p i))
          (Endpoints.CM.Construction.realizedVector E (NegRealization.CM.SurfaceConstruction.negRealization E (v (Fin.natAdd p i)) (R (Fin.natAdd p i)))
            (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E))) =
      (fun i => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g i) (Endpoints.CM.Construction.realizedVector E (R i) 1)) := by
    funext i
    obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin p ⊕ Fin p ≃ Fin (p + p)).surjective i
    cases j with
    | inl j => rw [finSumFinEquiv_apply_left, Fin.append_left]
    | inr j =>
      rw [finSumFinEquiv_apply_right, Fin.append_right]
      exact congrArg (fun x => Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (g (Fin.natAdd p j)) x)
        (NegRealization.CM.SurfaceConstruction.negRealization_at_conjugation E (v (Fin.natAdd p j)) (R (Fin.natAdd p j)))
  erw [heq] at h
  exact h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMReduction.CanonicalTuple.CM.Construction
