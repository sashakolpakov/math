import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Localized.TensorSubmoduleDetection
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.RelationsBaseChangeMap

/-! # Ideal Localization Detection -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealLocalizationDetection.GradedHilbert

noncomputable section

/-! Homogeneous ideals are detected after coefficient localization at all
maximal ideals of the base ring, without noetherianity. -/

universe u
variable {R : Type u} [CommRing R] {n : ℕ}

theorem homogeneousIdeal_eq_of_coefficient_localizations
    (I J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (h : ∀ p : Ideal R, ∀ _ : p.IsMaximal,
      Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p) I =
        Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := Localization.AtPrime p) J) : I = J := by
  have hd (d : ℕ) : Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d = Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d := by
    apply Localized.TensorSubmoduleDetection.submodule_eq_of_localized_tensor
    intro p hp
    apply Submodule.map_injective_of_injective
      (CoefficientBaseChange.GradedHilbert.homogeneousPieceBaseChangeEquiv (R := R) (S := Localization.AtPrime p) (n := n) d).injective
    rw [RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, RelationsBaseChangeMap.GradedHilbert.degreeRelations_baseChange_map, h p hp]
  apply HomogeneousIdeal.ext'
  intro d f hf
  change (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n d) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d ↔
    (⟨f, hf⟩ : Hilbert.Polynomial.GradedHilbert.grading R n d) ∈ Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d
  rw [hd]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealLocalizationDetection.GradedHilbert
