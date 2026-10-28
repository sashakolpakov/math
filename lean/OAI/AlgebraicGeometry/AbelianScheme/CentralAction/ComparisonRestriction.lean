import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocallyComparedDescent
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomRebase

/-! # Comparison Restriction -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ComparisonRestriction

noncomputable section

/-! A compatible line comparison descends after any change of base on
which the two target line bundles admit a reference isomorphism. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

theorem comparison_desc_on_base {S : Scheme.{0}} {Y X U V : Over S}
    (f : X ⟶ Y) (i : U ⟶ Y) (p : V ⟶ X) (r : V ⟶ U) (h : p ≫ f = r ≫ i)
    [EffectiveEpi r.left] [Surjective r.left] (L M : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle Y.left)
    (b : (L.pullback i.left).sheaf ≅ (M.pullback i.left).sheaf) :
    let F := LinePullHom.Construction.overSchemeModulePullbacks S
    ∀ a : (F.map f.op.toLoc).toFunctor.obj L.sheaf ≅
        (F.map f.op.toLoc).toFunctor.obj M.sheaf,
      (∀ (T : Over S) (s t : T ⟶ X) (w : T ⟶ Y) (hs : s ≫ f = w) (ht : t ≫ f = w),
        pullHom (F := F) a.hom s w w hs hs = pullHom (F := F) a.hom t w w ht ht) →
      ∃ d : (L.pullback i.left).sheaf ≅ (M.pullback i.left).sheaf,
        pullHom (F := F) d.hom r (r ≫ i) (r ≫ i) rfl rfl =
          pullHom (F := F) a.hom p (r ≫ i) (r ≫ i) h h := by
  dsimp only
  intro a ha
  let F := LinePullHom.Construction.overSchemeModulePullbacks S
  let a₀ := pullHom (F := F) a.hom p (r ≫ i) (r ≫ i) h h
  have ha₀ : IsIso a₀ := PullHomNormalization.Construction.pullHom_isIso F a.hom p (r ≫ i) (r ≫ i) h h
  let a₁ := PullHomRebase.Construction.rebaseLineHom F i r a₀
  have ha₁ : IsIso a₁ := PullHomRebase.Construction.rebaseLineHom_isIso F i r a₀
  have hc (T : Over S) (s t : T ⟶ V) (hst : s ≫ r = t ≫ r) :
      pullHom (F := F) a₁ s (s ≫ r) (s ≫ r) rfl rfl =
        pullHom (F := F) a₁ t (s ≫ r) (s ≫ r) hst.symm hst.symm := by
    apply PullHomRebase.Construction.rebaseLineHom_compatible F i r a₀ _ s t hst
    intro W s t w hs ht
    exact PullHomRebase.Construction.pullHom_compatible_pullback F f a.hom ha p (r ≫ i) h s t w hs ht
  obtain ⟨d, hd⟩ := LocallyComparedDescent.Construction.line_iso_desc_of_reference r (L.pullback i.left) (M.pullback i.left)
    b (@asIso _ _ _ _ a₁ ha₁) hc
  refine ⟨d, ?_⟩
  apply PullHomRebase.Construction.rebaseLineHom_injective F i r
  rw [PullHomRebase.Construction.rebaseLineHom_pullback_map]
  exact hd

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.ComparisonRestriction
