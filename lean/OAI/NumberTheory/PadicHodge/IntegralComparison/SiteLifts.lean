import Mathlib

/-! # Site Lifts -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts

noncomputable section

/-!
# IntegralComparison: continuity from lifts of incoming morphisms

A functor which lifts incoming arrows up to isomorphism and is full on
commuting triangles preserves the pullback operation on sieves. Hence
preservation of generating covering families suffices for continuity.
These categorical conditions are verified for crystalline postcomposition
in the geometric application.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v u' v' w

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable (F : C ⥤ D)

structure IncomingLifts where
  object {U : C} {V : D} (α : V ⟶ F.obj U) : C
  iso {U : C} {V : D} (α : V ⟶ F.obj U) : F.obj (object α) ≅ V
  hom {U : C} {V : D} (α : V ⟶ F.obj U) : object α ⟶ U
  map_hom {U : C} {V : D} (α : V ⟶ F.obj U) : F.map (hom α) = (iso α).hom ≫ α
  fullTriangle {U V W : C} (a : U ⟶ W) (b : V ⟶ W)
    (c : F.obj U ⟶ F.obj V) (h : c ≫ F.map b = F.map a) :
    ∃ d : U ⟶ V, F.map d = c ∧ d ≫ b = a

variable {F} (L : IncomingLifts F)

namespace IncomingLifts

include L

lemma pushforward_pullback {U V : C} (a : V ⟶ U) (S : Sieve U) :
    (S.pullback a).functorPushforward F = (S.functorPushforward F).pullback (F.map a) := by
  refine le_antisymm (Sieve.functorPushforward_pullback_le F a S) ?_
  intro Z α hα
  obtain ⟨W, b, c, hb, h⟩ := hα
  have he : ((L.iso α).hom ≫ c) ≫ F.map b = F.map (L.hom α ≫ a) := by
    rw [F.map_comp, L.map_hom]
    simp only [Category.assoc]
    rw [← h]
  obtain ⟨d, _, hd⟩ := L.fullTriangle (L.hom α ≫ a) b ((L.iso α).hom ≫ c) he
  refine ⟨L.object α, L.hom α, (L.iso α).inv, ?_, ?_⟩
  · change S (L.hom α ≫ a)
    rw [← hd]
    exact S.downward_closed hb d
  · rw [L.map_hom]
    simp

lemma preserves_generated_topology (J : Precoverage C) (K : Precoverage D)
    (h : J ≤ K.comap F) : CoverPreserving J.toGrothendieck K.toGrothendieck F where
  cover_preserve {U S} hS := by
    induction hS with
    | of U R hR =>
      rw [← Sieve.generate_map_eq_functorPushforward]
      exact K.generate_mem_toGrothendieck (h U hR)
    | top U =>
      rw [Sieve.functorPushforward_top]
      exact K.toGrothendieck.top_mem _
    | pullback U S hS V a ih =>
      rw [L.pushforward_pullback]
      exact K.toGrothendieck.pullback_stable _ ih
    | transitive U S R hS hR ihS ihR =>
      apply K.toGrothendieck.transitive ihS
      intro V a ha
      obtain ⟨W, b, c, hb, rfl⟩ := ha
      rw [Sieve.pullback_comp]
      apply K.toGrothendieck.pullback_stable
      rw [← L.pushforward_pullback]
      exact ihR hb

lemma compatiblePreserving (K : GrothendieckTopology D) : CompatiblePreserving.{w} K F where
  compatible ℱ {Z T x} hx {Y₁ Y₂ W} a b {g₁ g₂} hg₁ hg₂ he := by
    let α := a ≫ F.map g₁
    let e := L.iso α
    let t := L.hom α
    have ht : F.map t = e.hom ≫ α := L.map_hom α
    obtain ⟨a', ha', hag₁⟩ := L.fullTriangle t g₁ (e.hom ≫ a) (by
      rw [ht]; exact Category.assoc _ _ _)
    obtain ⟨b', hb', hbg₂⟩ := L.fullTriangle t g₂ (e.hom ≫ b) (by
      rw [ht, Category.assoc, ← he])
    apply (ℱ.obj.mapIso e.op).toEquiv.injective
    have hc := hx a' b' hg₁ hg₂ (hag₁.trans hbg₂.symm)
    change ℱ.obj.map (F.map a').op (x g₁ hg₁) =
      ℱ.obj.map (F.map b').op (x g₂ hg₂) at hc
    rw [ha', hb'] at hc
    simpa using hc

theorem continuous (J : Precoverage C) (K : Precoverage D) (h : J ≤ K.comap F) :
    F.IsContinuous J.toGrothendieck K.toGrothendieck :=
  Functor.isContinuous_of_coverPreserving (L.compatiblePreserving K.toGrothendieck)
    (L.preserves_generated_topology J K h)

end IncomingLifts

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SiteLifts
