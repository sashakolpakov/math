import OAI.RepresentationTheory.Theta.Geometric.FlatSourceLocalizations
import Mathlib.AlgebraicGeometry.Morphisms.FlatMono

/-! # Mono Stalk Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoStalkSections

noncomputable section

/-! A quasi-compact monomorphism with sections over every actual base
local ring is an isomorphism. Nilpotents remain visible in these tests. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

theorem mono_isIso_of_stalk_sections {X S : Scheme.{u}}
    (f : X ⟶ S) [Mono f] [QuasiCompact f]
    (h : ∀ x : S, ∃ t : Spec (S.presheaf.stalk x) ⟶ X,
      t ≫ f = S.fromSpecStalk x) : IsIso f := by
  have hp (x : S) : IsIso (pullback.snd f (S.fromSpecStalk x)) := by
    obtain ⟨t, ht⟩ := h x
    let s := pullback.lift t (𝟙 _) (ht.trans (Category.id_comp _).symm)
    have hs : s ≫ pullback.snd f (S.fromSpecStalk x) = 𝟙 _ := pullback.lift_snd _ _ _
    exact ⟨⟨s, by
      apply (cancel_mono (pullback.snd f (S.fromSpecStalk x))).mp
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp], hs⟩⟩
  have hflat : Flat (f ≫ 𝟙 S) := RepresentationTheory.Theta.Geometric.FlatSourceLocalizations.flat_of_ambient_stalk_localizations f (𝟙 S) (by
    intro z
    rw [Category.comp_id, pullback.condition]
    have := hp (f z)
    have := FormalGeometry.Completion.StalkFlat.Construction.scheme_fromSpecStalk_flat S (f z)
    infer_instance)
  have : Flat f := by simpa only [Category.comp_id] using hflat
  have : Surjective f := by
    constructor
    intro x
    obtain ⟨t, ht⟩ := h x
    refine ⟨t (IsLocalRing.closedPoint (S.presheaf.stalk x)), ?_⟩
    exact (congrArg (fun a : Spec (S.presheaf.stalk x) ⟶ S =>
      a (IsLocalRing.closedPoint (S.presheaf.stalk x))) ht).trans Scheme.fromSpecStalk_closedPoint
  exact Flat.isIso_of_surjective_of_mono f

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.MonoStalkSections
