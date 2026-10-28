import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.LocalIsoRepresentation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RepresentedIsoMonomorphism

/-! # Local Fine Iso Parameter -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.LocalFineIsoParameter

noncomputable section

/-! At full level at least three, a quasi-projective monomorphism representing the complete polarized isomorphism functor is constructed near every point of a locally Noetherian base. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem polarizedIso_exists_local_quasiProjective_monomorphism
    {S : Scheme.{u}} [IsLocallyNoetherian S] {g N : ℕ} {δ : Fin g → ℕ}
    (A B : PolarizationData.PolarizedAbelianWithFullLevel g δ N S) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N) (x : S) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ S), IsOpenImmersion f ∧ x ∈ Set.range f ∧
      ∃ M : Over Y, Nonempty (Projective.ProjectivePresentations.QuasiProjectivePresentation M) ∧ Mono M.hom ∧
        Nonempty (Family.LevelIsoFunctor.familyLevelIsoFunctor (A.pullback f) (B.pullback f) ≅ yoneda.obj M) := by
  have : NeZero N := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 3) hN)⟩
  obtain ⟨Y, f, hf, hx, M, hM, ⟨e⟩⟩ := LocalIsoRepresentation.polarizedIso_exists_local_quasiProjective_representation A B hδ x
  have : IsLocallyNoetherian Y := @isLocallyNoetherian_of_isOpenImmersion Y S f hf inferInstance
  exact ⟨Y, f, hf, hx, M, hM,
    RepresentedIsoMonomorphism.representedPolarizedIsoParameter_mono (A.pullback f) (B.pullback f) hN M e, ⟨e⟩⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Zariski.LocalFineIsoParameter
