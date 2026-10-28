import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure.Fine
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.TestUniqueness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Rational.PolarizedNoetherianModel

/-! # Fine Noetherian Tests -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure

noncomputable section

/-! Reduction steps for the original pure fine-moduli property. A
concrete quasi-projective model that classifies Noetherian families has
unique parameter points on all tests. The actual rational Noetherian
model of an affine family then supplies its classifying map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {g N : ℕ} {δ : Fin g → ℕ}

theorem Fine.PurePolarizedModel.points_eq_of_noetherian_classification
    {S : Scheme.{0}} [IsNoetherian S]
    (M : Fine.PurePolarizedModel g δ N S) (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)
    (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hM : ∀ (V : Over S), IsNoetherian V.left →
      ∀ (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N V.left),
        ∃! c : V ⟶ M.space, Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) B))
    {T : Over S} (a b : T ⟶ M.space)
    (hab : Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback a.left) (M.universal.pullback b.left))) :
    a = b := by
  apply HilbertConstruction.Noetherian.TestUniqueness.polarizedParameterPoints_eq_of_noetherianTests Q M.universal hδ hN _ a b hab
  intro V hV f k hfk
  obtain ⟨c, _, hc⟩ := hM V hV (M.universal.pullback f.left)
  obtain ⟨e⟩ := hfk
  exact (hc f ⟨HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.refl _⟩).trans (hc k ⟨e.symm⟩).symm

theorem Fine.PurePolarizedModel.classifies_affine_of_noetherian_classification
    (M : Fine.PurePolarizedModel g δ N (Spec (.of ℚ)))
    (Q : HilbertConstruction.Projective.ProjectivePresentations.QuasiProjectivePresentation M.space)
    (hg : 0 < g) (hδ : ∀ i, 0 < δ i) (hN : 3 ≤ N)
    (hM : ∀ (V : Over (Spec (.of ℚ))), IsNoetherian V.left →
      ∀ (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N V.left),
        ∃! c : V ⟶ M.space, Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) B))
    (T : Over (Spec (.of ℚ))) [IsAffine T.left]
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N T.left) :
    ∃! c : T ⟶ M.space, Nonempty (HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) A) := by
  obtain ⟨V, hV, B, t, ⟨e⟩⟩ := A.exists_rationalNoetherianModel T.hom hg hδ hN
  obtain ⟨b, ⟨eb⟩, _⟩ := hM V hV B
  let c : T ⟶ M.space := t ≫ b
  let ec : HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso (M.universal.pullback c.left) A :=
    (((HilbertConstruction.Moduli.Isomorphisms.LevelPreservingIso.pullbackComp M.universal b.left t.left).symm.trans
      (eb.pullback t.left)).trans e.symm)
  refine ⟨c, ⟨ec⟩, ?_⟩
  intro k hk
  obtain ⟨ek⟩ := hk
  exact M.points_eq_of_noetherian_classification Q hδ hN hM k c ⟨ek.trans ec.symm⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pure
