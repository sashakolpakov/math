import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.AffineNeighborhoods
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Connected.IsoRepresentation

/-! # Local Iso Representation -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.LocalIsoRepresentation

noncomputable section

/-! The full polarized isomorphism functor has a constructed quasi-projective representation on a neighborhood of every point of a locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem polarizedIso_exists_local_quasiProjective_representation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} [NeZero N] {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) (x : S) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ S), IsOpenImmersion f ∧ x ∈ Set.range f ∧
      ∃ M : Over Y, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧
        Nonempty (Family.LevelIsoFunctor.familyLevelIsoFunctor (A.pullback f) (B.pullback f) ≅ yoneda.obj M) := by
  obtain ⟨Y, f, hf, hY, hN, hc, hx⟩ := Connected.AffineNeighborhoods.exists_connected_affine_openNeighborhood S x
  obtain ⟨M, hM, he⟩ := Connected.IsoRepresentation.connectedNoetherianAffine_polarizedIso_quasiProjective_representation
    (A.pullback f) (B.pullback f) hδ
  exact ⟨Y, f, hf, hx, M, hM, he⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.LocalIsoRepresentation
