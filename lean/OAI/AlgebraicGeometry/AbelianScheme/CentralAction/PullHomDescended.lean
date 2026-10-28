import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomRebase
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LinePullHom

/-! # Pull Hom Descended -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomDescended.Construction

noncomputable section

/-! The exact descent equation remains valid on every further test. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

theorem pullHom_descended_transport
    {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {Y X U V T : C} (f : X ⟶ Y) (i : U ⟶ Y)
    (p : V ⟶ X) (r : V ⟶ U) (h : p ≫ f = r ≫ i)
    {L M : F.obj (.mk (op Y))}
    (a : (F.map f.op.toLoc).toFunctor.obj L ⟶ (F.map f.op.toLoc).toFunctor.obj M)
    (d : (F.map i.op.toLoc).toFunctor.obj L ⟶ (F.map i.op.toLoc).toFunctor.obj M)
    (hd : pullHom d r (r ≫ i) (r ≫ i) rfl rfl = pullHom a p (r ≫ i) (r ≫ i) h h)
    (k : T ⟶ V) (s : T ⟶ U) (t : T ⟶ X) (w : T ⟶ Y)
    (hs : k ≫ r = s) (ht : k ≫ p = t) (hsi : s ≫ i = w) (htf : t ≫ f = w) :
    pullHom d s w w hsi hsi = pullHom a t w w htf htf := by
  have hk : k ≫ (r ≫ i) = w := by rw [← Category.assoc, hs, hsi]
  have H := congrArg (fun b => pullHom b k w w hk hk) hd
  rw [pullHom_pullHom, pullHom_pullHom] at H
  simpa only [hs, ht] using H

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomDescended.Construction
