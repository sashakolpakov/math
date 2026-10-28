import OAI.AlgebraicGeometry.Picard.PoincareBundle.DescentReindexing
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! # Underlying Descent -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent

noncomputable section

/-!
# Descent data over a fixed base give descent data on the underlying objects
-/

open _root_.CategoryTheory Opposite

universe u v w₁ w₂ t

variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{w₁,w₂})
  {S : C} {ι : Type t} {A : ι → Over S} {B : Over S} (f : ∀ i, A i ⟶ B)

/-- A test object mapping to the quotient has its canonical structure over the original base. -/
def testObject {T : C} (q : T ⟶ B.left) : Over S := Over.mk (q ≫ B.hom)

def baseMap {T : C} (q : T ⟶ B.left) : testObject q ⟶ B := Over.homMk q rfl

def coverMap {T : C} (q : T ⟶ B.left) {i : ι} (x : T ⟶ (A i).left)
    (hx : x ≫ (f i).left = q) : testObject q ⟶ A i :=
  Over.homMk x (by
    change x ≫ (A i).hom = q ≫ B.hom
    rw [← Over.w (f i), ← Category.assoc, hx])

theorem coverMap_base {T : C} (q : T ⟶ B.left) {i : ι} (x : T ⟶ (A i).left)
    (hx : x ≫ (f i).left = q) : coverMap f q x hx ≫ f i = baseMap q :=
  Over.OverMorphism.ext hx

def testMap {T T' : C} (g : T' ⟶ T) (q : T ⟶ B.left) (q' : T' ⟶ B.left)
    (hq : g ≫ q = q') : testObject q' ⟶ testObject q :=
  Over.homMk g (by change g ≫ (q ≫ B.hom) = q' ≫ B.hom; rw [← Category.assoc, hq])

theorem testMap_base {T T' : C} (g : T' ⟶ T) (q : T ⟶ B.left) (q' : T' ⟶ B.left)
    (hq : g ≫ q = q') : testMap g q q' hq ≫ baseMap q = baseMap q' :=
  Over.OverMorphism.ext hq

theorem testMap_cover {T T' : C} (g : T' ⟶ T) (q : T ⟶ B.left) (q' : T' ⟶ B.left)
    (hq : g ≫ q = q') {i : ι} (x : T ⟶ (A i).left) (hx : x ≫ (f i).left = q)
    (x' : T' ⟶ (A i).left) (hx' : x' ≫ (f i).left = q') (hgx : g ≫ x = x') :
    testMap g q q' hq ≫ coverMap f q x hx = coverMap f q' x' hx' :=
  Over.OverMorphism.ext hgx

variable (D : (DescentReindexing.reindex (Over.forget S) F).DescentData f)

/-- The underlying descent morphism is evaluated on the canonically induced object over the base. -/
def underlyingHom {T : C} (q : T ⟶ B.left) {i j : ι}
    (x : T ⟶ (A i).left) (y : T ⟶ (A j).left)
    (hx : x ≫ (f i).left = q) (hy : y ≫ (f j).left = q) :
    (F.map x.op.toLoc).toFunctor.obj (D.obj i) ⟶ (F.map y.op.toLoc).toFunctor.obj (D.obj j) :=
  D.hom (baseMap q) (coverMap f q x hx) (coverMap f q y hy)
    (coverMap_base f q x hx) (coverMap_base f q y hy)

theorem underlyingHom_pullback {T T' : C} (g : T' ⟶ T) (q : T ⟶ B.left) (q' : T' ⟶ B.left)
    (hq : g ≫ q = q') {i j : ι} (x : T ⟶ (A i).left) (y : T ⟶ (A j).left)
    (hx : x ≫ (f i).left = q) (hy : y ≫ (f j).left = q)
    (x' : T' ⟶ (A i).left) (y' : T' ⟶ (A j).left)
    (hgx : g ≫ x = x') (hgy : g ≫ y = y') :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := F)
        (underlyingHom F f D q x y hx hy) g x' y' hgx hgy =
      underlyingHom F f D q' x' y'
        (by rw [← hgx, Category.assoc, hx, hq]) (by rw [← hgy, Category.assoc, hy, hq]) := by
  have hx' : x' ≫ (f i).left = q' := by rw [← hgx, Category.assoc, hx, hq]
  have hy' : y' ≫ (f j).left = q' := by rw [← hgy, Category.assoc, hy, hq]
  have hp := DescentReindexing.pullHom_reindex (Over.forget S) F
    (D.hom (baseMap q) (coverMap f q x hx) (coverMap f q y hy)
      (coverMap_base f q x hx) (coverMap_base f q y hy))
    (testMap g q q' hq) (coverMap f q' x' hx') (coverMap f q' y' hy')
    (testMap_cover f g q q' hq x hx x' hx' hgx)
    (testMap_cover f g q q' hq y hy y' hy' hgy)
  exact hp.symm.trans (D.pullHom_hom (testMap g q q' hq) (baseMap q) (baseMap q')
    (testMap_base g q q' hq) (coverMap f q x hx) (coverMap f q y hy)
    (coverMap_base f q x hx) (coverMap_base f q y hy)
    (coverMap f q' x' hx') (coverMap f q' y' hy')
    (testMap_cover f g q q' hq x hx x' hx' hgx)
    (testMap_cover f g q q' hq y hy y' hy' hgy))

/-- Forgetting the fixed base preserves ordinary descent data on every test object. -/
def underlyingDatum : F.DescentData (fun i => (f i).left) where
  obj i := D.obj i
  hom := fun {_T} q {_i _j} x y hx hy => underlyingHom F f D q x y hx hy
  pullHom_hom := fun {_T' _T} g q q' hq {_i _j} x y hx hy x' y' hgx hgy =>
    underlyingHom_pullback F f D g q q' hq x y hx hy x' y' hgx hgy
  hom_self := fun {_T} q {_i} x hx =>
    D.hom_self (baseMap q) (coverMap f q x hx) (coverMap_base f q x hx)
  hom_comp := fun {_T} q {_i _j _k} x y z hx hy hz => D.hom_comp (baseMap q)
    (coverMap f q x hx) (coverMap f q y hy) (coverMap f q z hz)
    (coverMap_base f q x hx) (coverMap_base f q y hy) (coverMap_base f q z hz)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.UnderlyingDescent
