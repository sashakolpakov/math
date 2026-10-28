import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Normalization Restriction -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizationRestriction

noncomputable section

/-! Restriction of a normalization equation in a pullback pseudofunctor.
Using the comparison between the two zero fibers avoids arbitrary choices
of a trivialization on each overlap. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
variable {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'}}
variable {B Y T V T' V' : C} {M N : F.obj (.mk (op Y))}

def IsNormalized (z : B ⟶ Y) (t : T ⟶ B) (s : V ⟶ Y) (zt : T ⟶ V)
    (h : zt ≫ s = t ≫ z)
    (q : (F.map s.op.toLoc).toFunctor.obj M ⟶ (F.map s.op.toLoc).toFunctor.obj N)
    (q₀ : (F.map z.op.toLoc).toFunctor.obj M ⟶ (F.map z.op.toLoc).toFunctor.obj N) : Prop :=
  pullHom q zt (t ≫ z) (t ≫ z) h h = pullHom q₀ t (t ≫ z) (t ≫ z) rfl rfl

theorem normalized_restrict (z : B ⟶ Y) (t : T ⟶ B) (s : V ⟶ Y) (zt : T ⟶ V)
    (h : zt ≫ s = t ≫ z)
    (q : (F.map s.op.toLoc).toFunctor.obj M ⟶ (F.map s.op.toLoc).toFunctor.obj N)
    (q₀ : (F.map z.op.toLoc).toFunctor.obj M ⟶ (F.map z.op.toLoc).toFunctor.obj N)
    (hq : IsNormalized z t s zt h q q₀)
    (a : V' ⟶ V) (b : T' ⟶ T) (t' : T' ⟶ B) (s' : V' ⟶ Y) (zt' : T' ⟶ V')
    (ht : b ≫ t = t') (hs : a ≫ s = s') (hz : zt' ≫ a = b ≫ zt)
    (h' : zt' ≫ s' = t' ≫ z) :
    IsNormalized z t' s' zt' h' (pullHom q a s' s' hs hs) q₀ := by
  have hb : b ≫ (t ≫ z) = t' ≫ z := by rw [← Category.assoc, ht]
  have ha : (zt' ≫ a) ≫ s = t' ≫ z := by rw [Category.assoc, hs, h']
  have hc : (b ≫ zt) ≫ s = t' ≫ z := by rw [Category.assoc, h, hb]
  change pullHom (pullHom q a s' s' hs hs) zt' (t' ≫ z) (t' ≫ z) h' h' = _
  calc
    _ = pullHom q (zt' ≫ a) (t' ≫ z) (t' ≫ z) ha ha :=
      pullHom_pullHom q a s' s' zt' (t' ≫ z) (t' ≫ z) hs hs h' h'
    _ = pullHom q (b ≫ zt) (t' ≫ z) (t' ≫ z) hc hc :=
      Picard.PoincareBundle.PullHom.pullHom_congr q _ _ hz _ _ ha ha hc hc
    _ = pullHom (pullHom q zt (t ≫ z) (t ≫ z) h h) b (t' ≫ z) (t' ≫ z) hb hb :=
      (pullHom_pullHom q zt (t ≫ z) (t ≫ z) b (t' ≫ z) (t' ≫ z) h h hb hb).symm
    _ = pullHom (pullHom q₀ t (t ≫ z) (t ≫ z) rfl rfl) b (t' ≫ z) (t' ≫ z) hb hb :=
      congrArg (fun r ↦ pullHom r b (t' ≫ z) (t' ≫ z) hb hb) hq
    _ = pullHom q₀ (b ≫ t) (t' ≫ z) (t' ≫ z)
        (by rw [ht]) (by rw [ht]) :=
      pullHom_pullHom q₀ t (t ≫ z) (t ≫ z) b (t' ≫ z) (t' ≫ z) rfl rfl hb hb
    _ = pullHom q₀ t' (t' ≫ z) (t' ≫ z) rfl rfl :=
      Picard.PoincareBundle.PullHom.pullHom_congr q₀ _ _ ht _ _ _ _ rfl rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.NormalizationRestriction
