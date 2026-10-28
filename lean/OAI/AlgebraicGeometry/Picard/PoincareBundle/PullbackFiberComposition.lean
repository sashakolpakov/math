import OAI.AlgebraicGeometry.Picard.PoincareBundle.PullHom

/-! # Pullback Fiber Composition -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition

noncomputable section

/-!
# Composition comparisons for fibers of a pulled-back object commute with native geometric pullback
-/

open _root_.CategoryTheory Opposite
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

universe u v u' v'

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
  {E Z : C} (p : E ⟶ Z) (L : F.obj (.mk (op Z)))

/-- The actual composition isomorphism identifies a fiber of the pulled-back object with its original fiber. -/
def fiberIso {T : C} (x : T ⟶ E) :
    (F.map x.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) ≅
      (F.map (x ≫ p).op.toLoc).toFunctor.obj L :=
  (Cat.Hom.toNatIso (F.mapComp' p.op.toLoc x.op.toLoc (x ≫ p).op.toLoc rfl)).symm.app L

/-- The same actual composition comparison with an explicitly specified composite point. -/
def fiberIsoTo {T : C} (k : T ⟶ E) (x : T ⟶ Z) (hk : k ≫ p = x) :
    (F.map k.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) ≅
      (F.map x.op.toLoc).toFunctor.obj L :=
  (Cat.Hom.toNatIso (F.mapComp' p.op.toLoc k.op.toLoc x.op.toLoc (by rw [← hk]; rfl))).symm.app L

/-- Native pullback preserves composition comparisons with specified endpoint equalities. -/
theorem fiberIsoTo_hom_pullback {T T' : C} (g : T' ⟶ T) (k : T ⟶ E) (x : T ⟶ Z)
    (hk : k ≫ p = x) (k' : T' ⟶ E) (x' : T' ⟶ Z) (hk' : k' ≫ p = x')
    (hgk : g ≫ k = k') (hgx : g ≫ x = x') :
    pullHom (fiberIsoTo F p L k x hk).hom g k' x' hgk hgx = (fiberIsoTo F p L k' x' hk').hom := by
  unfold pullHom fiberIsoTo
  have h := F.mapComp'₀₁₃_inv_app p.op.toLoc k.op.toLoc g.op.toLoc
    x.op.toLoc k'.op.toLoc x'.op.toLoc (by rw [← hk]; rfl)
    (by rw [← hgk]; rfl) (by rw [← hk']; rfl) L
  exact h.symm

/-- Pseudofunctor associativity gives native pullback of the actual fiber comparison. -/
theorem fiberIso_hom_pullback {T T' : C} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (hxp : g ≫ (x ≫ p) = x' ≫ p) :
    pullHom (fiberIso F p L x).hom g x' (x' ≫ p) hx hxp = (fiberIso F p L x').hom := by
  unfold pullHom fiberIso
  have h := F.mapComp'₀₁₃_inv_app p.op.toLoc x.op.toLoc g.op.toLoc
    (x ≫ p).op.toLoc x'.op.toLoc (x' ≫ p).op.toLoc rfl
    (by rw [← hx]; rfl) rfl L
  exact h.symm

/-- Native pullback carries an actual fiber isomorphism to an actual fiber isomorphism. -/
def pullIso {A B T T' : C} {M : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    {x : T ⟶ A} {y : T ⟶ B}
    (e : (F.map x.op.toLoc).toFunctor.obj M ≅ (F.map y.op.toLoc).toFunctor.obj N)
    (g : T' ⟶ T) (x' : T' ⟶ A) (y' : T' ⟶ B) (hx : g ≫ x = x') (hy : g ≫ y = y') :
    (F.map x'.op.toLoc).toFunctor.obj M ≅ (F.map y'.op.toLoc).toFunctor.obj N where
  hom := pullHom e.hom g x' y' hx hy
  inv := pullHom e.inv g y' x' hy hx
  hom_inv_id := by
    rw [← PullHom.pullHom_comp e.hom e.inv g x' y' x' hx hy hx, e.hom_inv_id]
    exact PullHom.pullHom_identity g x' hx
  inv_hom_id := by
    rw [← PullHom.pullHom_comp e.inv e.hom g y' x' y' hy hx hy, e.inv_hom_id]
    exact PullHom.pullHom_identity g y' hy

/-- The whole fiber comparison isomorphism is preserved by change of test object. -/
theorem fiberIso_pullback {T T' : C} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (hxp : g ≫ (x ≫ p) = x' ≫ p) :
    pullIso F (fiberIso F p L x) g x' (x' ≫ p) hx hxp = fiberIso F p L x' := by
  apply Iso.ext
  exact fiberIso_hom_pullback F p L g x x' hx hxp

/-- Native pullback also preserves the inverse fiber comparison. -/
theorem fiberIso_inv_pullback {T T' : C} (g : T' ⟶ T) (x : T ⟶ E) (x' : T' ⟶ E)
    (hx : g ≫ x = x') (hxp : g ≫ (x ≫ p) = x' ≫ p) :
    pullHom (fiberIso F p L x).inv g (x' ≫ p) x' hxp hx = (fiberIso F p L x').inv :=
  congrArg Iso.inv (fiberIso_pullback F p L g x x' hx hxp)

/-- Transport a morphism of original fibers to the actual fibers of the pulled-back object. -/
def transport {T : C} (x y : T ⟶ E)
    (a : (F.map (x ≫ p).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ p).op.toLoc).toFunctor.obj L) :
    (F.map x.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) ⟶
      (F.map y.op.toLoc).toFunctor.obj ((F.map p.op.toLoc).toFunctor.obj L) :=
  (fiberIso F p L x).hom ≫ a ≫ (fiberIso F p L y).inv

/-- Pulling back a transported fiber operation agrees with transporting its genuine native pullback. -/
theorem transport_pullback {T T' : C} (g : T' ⟶ T) (x y : T ⟶ E)
    (a : (F.map (x ≫ p).op.toLoc).toFunctor.obj L ⟶ (F.map (y ≫ p).op.toLoc).toFunctor.obj L)
    (x' y' : T' ⟶ E) (hx : g ≫ x = x') (hy : g ≫ y = y')
    (hxp : g ≫ (x ≫ p) = x' ≫ p) (hyp : g ≫ (y ≫ p) = y' ≫ p) :
    pullHom (transport F p L x y a) g x' y' hx hy =
      transport F p L x' y' (pullHom a g (x' ≫ p) (y' ≫ p) hxp hyp) := by
  unfold transport
  rw [PullHom.pullHom_comp _ _ g x' (x' ≫ p) y' hx hxp hy,
    PullHom.pullHom_comp _ _ g (x' ≫ p) (y' ≫ p) y' hxp hyp hy,
    fiberIso_hom_pullback, fiberIso_inv_pullback]

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.PullbackFiberComposition
