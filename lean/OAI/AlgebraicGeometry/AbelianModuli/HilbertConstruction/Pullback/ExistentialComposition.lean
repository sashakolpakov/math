import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Existential Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ExistentialComposition

noncomputable section

section

/-! Transport through two actual pullback towers, retaining their
canonical reassociation isomorphism and projection maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- Transport through the original reassociation, transition, and projection. -/
def pullbackTowerTransportMap
    {C : Type*} [Category* C] [HasPullbacks C]
    {P F H P' F' H' O : C}
    (p : P ⟶ F) (f : F ⟶ H) (l : O ⟶ H)
    (q : P' ⟶ F') (g : F' ⟶ H') (r : O ⟶ H')
    (t : pullback f l ⟶ pullback g r)
    (s : pullback p (pullback.fst f l) ⟶ pullback q (t ≫ pullback.fst g r)) :
    pullback (p ≫ f) l ⟶ P' :=
  (pullbackRightPullbackFstIso f l p).inv ≫ s ≫ pullback.fst q (t ≫ pullback.fst g r)

theorem pullback_tower_transport
    {C : Type*} [Category* C] [HasPullbacks C]
    {P F H P' F' H' O : C}
    (p : P ⟶ F) (f : F ⟶ H) (l : O ⟶ H)
    (q : P' ⟶ F') (g : F' ⟶ H') (r : O ⟶ H')
    (t : pullback f l ⟶ pullback g r)
    (ht : t ≫ pullback.snd g r = pullback.snd f l)
    (s : pullback p (pullback.fst f l) ⟶ pullback q (t ≫ pullback.fst g r))
    (hs : s ≫ pullback.snd q (t ≫ pullback.fst g r) = pullback.snd p (pullback.fst f l)) :
    pullbackTowerTransportMap p f l q g r t s ≫ (q ≫ g) =
      pullback.snd (p ≫ f) l ≫ r := by
  let u := t ≫ pullback.fst g r
  let v := pullback.snd p (pullback.fst f l)
  let e := pullbackRightPullbackFstIso f l p
  have h1 : (s ≫ pullback.fst q u) ≫ q = v ≫ u := by
    rw [Category.assoc, pullback.condition (f := q) (g := u), ← Category.assoc, hs]
  have h2 : u ≫ g = pullback.snd f l ≫ r := by
    dsimp only [u]
    rw [Category.assoc, pullback.condition (f := g) (g := r), ← Category.assoc, ht]
  change (e.inv ≫ s ≫ pullback.fst q u) ≫ (q ≫ g) = _
  calc
    _ = e.inv ≫ (((s ≫ pullback.fst q u) ≫ q) ≫ g) := by simp only [Category.assoc]
    _ = e.inv ≫ ((v ≫ u) ≫ g) := congrArg (fun z => e.inv ≫ (z ≫ g)) h1
    _ = e.inv ≫ (v ≫ (u ≫ g)) := by simp only [Category.assoc]
    _ = e.inv ≫ (v ≫ (pullback.snd f l ≫ r)) := congrArg (fun z => e.inv ≫ (v ≫ z)) h2
    _ = (e.inv ≫ v ≫ pullback.snd f l) ≫ r := by simp only [Category.assoc]
    _ = _ := congrArg (fun z => z ≫ r) (pullbackRightPullbackFstIso_inv_snd_snd f l p)

/-- A lifted point has the prescribed image after transport. -/
theorem pullback_lift_comp_to_snd
    {C : Type*} [Category* C] [HasPullbacks C]
    {X B O Y T Z : C}
    (a : X ⟶ B) (l : O ⟶ B) (p : T ⟶ X) (b : T ⟶ O)
    (hp : p ≫ a = b ≫ l) (t : pullback a l ⟶ Y)
    (r : O ⟶ Z) (k : Y ⟶ Z)
    (ht : t ≫ k = pullback.snd a l ≫ r) :
    (pullback.lift p b hp ≫ t) ≫ k = b ≫ r := by
  rw [Category.assoc, ht, ← Category.assoc, pullback.lift_snd]

/-- The original lift into a pullback square, with a named generic boundary. -/
def isPullbackLiftMap
    {C : Type*} [Category* C] {P X Y Z T : C}
    {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback l r f g) (a : T ⟶ X) (b : T ⟶ Y)
    (hab : a ≫ f = b ≫ g) : T ⟶ P :=
  sq.lift a b hab

theorem isPullbackLiftMap_fst
    {C : Type*} [Category* C] {P X Y Z T : C}
    {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback l r f g) (a : T ⟶ X) (b : T ⟶ Y)
    (hab : a ≫ f = b ≫ g) :
    isPullbackLiftMap sq a b hab ≫ l = a :=
  sq.lift_fst a b hab

theorem isPullbackLiftMap_snd
    {C : Type*} [Category* C] {P X Y Z T : C}
    {l : P ⟶ X} {r : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (sq : IsPullback l r f g) (a : T ⟶ X) (b : T ⟶ Y)
    (hab : a ≫ f = b ≫ g) :
    isPullbackLiftMap sq a b hab ≫ r = b :=
  sq.lift_snd a b hab

end

/-! Compose the original chosen pullback lifts before specializing
their source objects. No projection proof is unpacked at a native base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

def composeExistentialPullbackLifts
    {C : Type*} [Category* C] [HasPullbacks C] {X B O Y T Z : C}
    (a : X ⟶ B) (l : O ⟶ B) (r : O ⟶ Z) (k : Y ⟶ Z)
    (p : T ⟶ X) (q : T ⟶ Z)
    (hb : ∃ b : T ⟶ O, b ≫ l = p ≫ a ∧ b ≫ r = q)
    (ht : ∃ t : pullback a l ⟶ Y, t ≫ k = pullback.snd a l ≫ r) : T ⟶ Y :=
  pullback.lift p hb.choose hb.choose_spec.1.symm ≫ ht.choose

theorem composeExistentialPullbackLifts_over
    {C : Type*} [Category* C] [HasPullbacks C] {X B O Y T Z : C}
    (a : X ⟶ B) (l : O ⟶ B) (r : O ⟶ Z) (k : Y ⟶ Z)
    (p : T ⟶ X) (q : T ⟶ Z)
    (hb : ∃ b : T ⟶ O, b ≫ l = p ≫ a ∧ b ≫ r = q)
    (ht : ∃ t : pullback a l ⟶ Y, t ≫ k = pullback.snd a l ≫ r) :
    composeExistentialPullbackLifts a l r k p q hb ht ≫ k = q :=
  (pullback_lift_comp_to_snd a l p hb.choose hb.choose_spec.1.symm
    ht.choose r k ht.choose_spec).trans hb.choose_spec.2

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ExistentialComposition
