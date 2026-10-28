import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomKernelPair

/-! # Pull Hom Rebase -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomRebase.Construction

noncomputable section

/-! Changing the base of a comparison preserves its native descent
compatibility, by the natural restriction isomorphism of Hom presheaves. -/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'
variable {C : Type u} [Category.{v} C]
    (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
    {Y X T W : C} {L M : F.obj (.mk (op Y))}

def rebaseLineHom (i : X ⟶ Y) (f : T ⟶ X)
    (a : (F.map (f ≫ i).op.toLoc).toFunctor.obj L ⟶
      (F.map (f ≫ i).op.toLoc).toFunctor.obj M) :
    (F.map f.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj L) ⟶
      (F.map f.op.toLoc).toFunctor.obj ((F.map i.op.toLoc).toFunctor.obj M) :=
  (F.overMapCompPresheafHomIso L M i).hom.app (op (Over.mk f)) a

theorem rebaseLineHom_injective (i : X ⟶ Y) (f : T ⟶ X) :
    Function.Injective (rebaseLineHom F (L := L) (M := M) i f) :=
  (ConcreteCategory.bijective_of_isIso
    ((F.overMapCompPresheafHomIso L M i).hom.app (op (Over.mk f)))).1

theorem rebaseLineHom_pullback_map (i : X ⟶ Y) (f : T ⟶ X)
    (b : (F.map i.op.toLoc).toFunctor.obj L ⟶ (F.map i.op.toLoc).toFunctor.obj M) :
    rebaseLineHom F i f (pullHom b f (f ≫ i) (f ≫ i) rfl rfl) =
      (F.map f.op.toLoc).toFunctor.map b := by
  let e := Cat.Hom.toNatIso (F.mapComp' i.op.toLoc f.op.toLoc (f ≫ i).op.toLoc rfl)
  change ((e.app L).inv ≫ ((e.app L).hom ≫ _ ≫ (e.app M).inv)) ≫ (e.app M).hom = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem pullHom_compatible_pullback {Z : C} (r : Z ⟶ Y)
    (a : (F.map r.op.toLoc).toFunctor.obj L ⟶ (F.map r.op.toLoc).toFunctor.obj M)
    (ha : ∀ (V : C) (p q : V ⟶ Z) (w : V ⟶ Y) (hp : p ≫ r = w) (hq : q ≫ r = w),
      pullHom a p w w hp hp = pullHom a q w w hq hq)
    (t : T ⟶ Z) (s : T ⟶ Y) (ht : t ≫ r = s)
    (p q : W ⟶ T) (w : W ⟶ Y) (hp : p ≫ s = w) (hq : q ≫ s = w) :
    pullHom (pullHom a t s s ht ht) p w w hp hp =
      pullHom (pullHom a t s s ht ht) q w w hq hq := by
  rw [pullHom_pullHom, pullHom_pullHom]
  apply ha

theorem rebaseLineHom_isIso (i : X ⟶ Y) (f : T ⟶ X)
    (a : (F.map (f ≫ i).op.toLoc).toFunctor.obj L ⟶
      (F.map (f ≫ i).op.toLoc).toFunctor.obj M) [IsIso a] :
    IsIso (rebaseLineHom F i f a) := by
  let e := Cat.Hom.toNatIso (F.mapComp' i.op.toLoc f.op.toLoc (f ≫ i).op.toLoc rfl)
  change IsIso (((e.app L).inv ≫ a) ≫ (e.app M).hom)
  infer_instance

theorem rebaseLineHom_pullHom (i : X ⟶ Y) (f : T ⟶ X)
    (a : (F.map (f ≫ i).op.toLoc).toFunctor.obj L ⟶
      (F.map (f ≫ i).op.toLoc).toFunctor.obj M)
    (p : W ⟶ T) (f' : W ⟶ X) (hf : p ≫ f = f') :
    pullHom (rebaseLineHom F i f a) p f' f' hf hf =
      rebaseLineHom F i f'
        (pullHom a p (f' ≫ i) (f' ≫ i)
          (by rw [← Category.assoc, hf]) (by rw [← Category.assoc, hf])) := by
  let e := F.overMapCompPresheafHomIso L M i
  let p' : Over.mk f' ⟶ Over.mk f := Over.homMk p hf
  exact (ConcreteCategory.congr_hom (e.hom.naturality p'.op) a).symm

theorem rebaseLineHom_compatible (i : X ⟶ Y) (f : T ⟶ X)
    (a : (F.map (f ≫ i).op.toLoc).toFunctor.obj L ⟶
      (F.map (f ≫ i).op.toLoc).toFunctor.obj M)
    (ha : ∀ (V : C) (p q : V ⟶ T) (w : V ⟶ Y)
        (hp : p ≫ f ≫ i = w) (hq : q ≫ f ≫ i = w),
      pullHom a p w w hp hp = pullHom a q w w hq hq)
    (p q : W ⟶ T) (hpq : p ≫ f = q ≫ f) :
    pullHom (rebaseLineHom F i f a) p (p ≫ f) (p ≫ f) rfl rfl =
      pullHom (rebaseLineHom F i f a) q (p ≫ f) (p ≫ f) hpq.symm hpq.symm := by
  rw [rebaseLineHom_pullHom, rebaseLineHom_pullHom]
  congr 1
  exact ha W p q ((p ≫ f) ≫ i) (Category.assoc _ _ _).symm
    (by rw [← Category.assoc, ← hpq])

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullHomRebase.Construction
