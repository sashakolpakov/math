import OAI.AlgebraicGeometry.HilbertScheme.Presentations.PowerSeriesPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.CompletionQuotientCoordinates

/-! # Completion Noetherian -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.CompletionNoetherian

noncomputable section

/-! The completion of a Noetherian ring along a principal ideal is
Noetherian, by a surjective power-series presentation. -/

universe u
variable (R : Type u) [CommRing R] [IsNoetherianRing R]

theorem principal_completion_isNoetherian (s : R) :
    IsNoetherianRing (AdicCompletion (Ideal.span {s}) R) := by
  let I : Ideal R := Ideal.span {s}
  let A := AdicCompletion I R
  let J : Ideal A := I.map (algebraMap R A)
  have hI : I.FG := Submodule.fg_span_singleton s
  let : IsAdicComplete J A :=
    (IsAdicComplete.map_algebraMap_iff I A).mpr (AdicCompletion.isAdicComplete hI)
  apply PowerSeriesPresentation.complete_principal_isNoetherian R A s J
  · simp only [J, I, Ideal.map_span, Set.image_singleton]
  · exact CompletionQuotientCoordinates.completion_residue_base_surjective I hI

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Principal.CompletionNoetherian
