import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Descent Object Iso -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentObjectIso

noncomputable section

/-!
# Transport ordinary descent data through an isomorphism of its actual source object
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})

/-- Native geometric pullback of a map already pulled to a test point is its pullback to the new point. -/
theorem pullHom_map {A T T' : C} {M N : F.obj (.mk (op A))} (e : M ⟶ N)
    (x : T ⟶ A) (g : T' ⟶ T) (x' : T' ⟶ A) (hx : g ≫ x = x') :
    pullHom ((F.map x.op.toLoc).toFunctor.map e) g x' x' hx hx =
      (F.map x'.op.toLoc).toFunctor.map e := by
  let c := Cat.Hom.toNatIso (F.mapComp' x.op.toLoc g.op.toLoc x'.op.toLoc (by rw [← hx]; rfl))
  change c.hom.app M ≫ (F.map x.op.toLoc ≫ F.map g.op.toLoc).toFunctor.map e ≫
    c.inv.app N = (F.map x'.op.toLoc).toFunctor.map e
  rw [← c.hom.naturality_assoc, c.hom_inv_id_app, Category.comp_id]

variable {A B : C} (f : A ⟶ B) (D : F.DescentData (fun (_ : PUnit.{1}) => f))
  (L : F.obj (.mk (op A))) (e : L ≅ D.obj PUnit.unit)

/-- Conjugate the original geometric gluing by the actual pulled-back source-object isomorphisms. -/
def transportedHom {T : C} (q : T ⟶ B) (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q) :
    (F.map x.op.toLoc).toFunctor.obj L ⟶ (F.map y.op.toLoc).toFunctor.obj L :=
  (F.map x.op.toLoc).toFunctor.map e.hom ≫
    D.hom q (i₁ := PUnit.unit) (i₂ := PUnit.unit) x y hx hy ≫
      (F.map y.op.toLoc).toFunctor.map e.inv

/-- Conjugated gluing retains the original diagonal identity. -/
theorem transportedHom_self {T : C} (q : T ⟶ B) (x : T ⟶ A) (hx : x ≫ f = q) :
    transportedHom F f D L e q x x hx hx = 𝟙 _ := by
  unfold transportedHom
  rw [D.hom_self q (i := PUnit.unit) x hx, Category.id_comp, ← Functor.map_comp, e.hom_inv_id,
    (F.map x.op.toLoc).toFunctor.map_id]

/-- Conjugated gluing retains the full original cocycle. -/
theorem transportedHom_comp {T : C} (q : T ⟶ B) (x y z : T ⟶ A)
    (hx : x ≫ f = q) (hy : y ≫ f = q) (hz : z ≫ f = q) :
    transportedHom F f D L e q x y hx hy ≫ transportedHom F f D L e q y z hy hz =
      transportedHom F f D L e q x z hx hz := by
  unfold transportedHom
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [← Functor.map_comp, e.inv_hom_id, (F.map y.op.toLoc).toFunctor.map_id]
  rw [Category.id_comp, ← Category.assoc (D.hom q x y hx hy), D.hom_comp]

/-- Conjugated gluing retains the native pullback law on arbitrary test objects. -/
theorem transportedHom_pullback {T T' : C} (g : T' ⟶ T) (q : T ⟶ B) (q' : T' ⟶ B)
    (hq : g ≫ q = q') (x y : T ⟶ A) (hx : x ≫ f = q) (hy : y ≫ f = q)
    (x' y' : T' ⟶ A) (hx' : x' ≫ f = q') (hy' : y' ≫ f = q')
    (hgx : g ≫ x = x') (hgy : g ≫ y = y') :
    pullHom (transportedHom F f D L e q x y hx hy) g x' y' hgx hgy =
      transportedHom F f D L e q' x' y' hx' hy' := by
  unfold transportedHom
  rw [PullHom.pullHom_comp _ _ g x' x' y' hgx hgx hgy,
    PullHom.pullHom_comp _ _ g x' y' y' hgx hgy hgy,
    pullHom_map, pullHom_map, D.pullHom_hom g q q' hq x y hx hy x' y' hgx hgy]

/-- Ordinary descent data on a pulled-back object can be transferred to an isomorphic original object. -/
def ofIso : F.DescentData (fun (_ : PUnit.{1}) => f) where
  obj _ := L
  hom _T q _i _j x y hx hy := transportedHom F f D L e q x y hx hy
  pullHom_hom _T' _T g q q' hq _i _j x y hx hy x' y' hgx hgy :=
    transportedHom_pullback F f D L e g q q' hq x y hx hy x' y' _ _ hgx hgy
  hom_self _T q _i x hx := transportedHom_self F f D L e q x hx
  hom_comp _T q _i _j _k x y z hx hy hz := transportedHom_comp F f D L e q x y z hx hy hz

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.DescentObjectIso
