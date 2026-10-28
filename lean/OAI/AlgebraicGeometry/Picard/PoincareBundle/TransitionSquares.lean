import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.NatIso

/-! # Transition Squares -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.TransitionSquares

noncomputable section

/-!
# Three commuting comparison squares identify a transition
-/

open _root_.CategoryTheory

variable {C D : Type*} [Category C] [Category D]

/-- Components of a three-step transition between functors. -/
theorem natural_transition_hom_app {F G H J : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : J ≅ H) (X : C) :
    (a ≪≫ b ≪≫ c.symm).hom.app X = a.hom.app X ≫ b.hom.app X ≫ c.inv.app X := rfl

/-- Evaluate a specified equality of natural transitions without unfolding its component functors. -/
theorem natural_transition_hom_of_eq {F G H J : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : J ≅ H) (e : F ≅ J)
    (h : e = a ≪≫ b ≪≫ c.symm) (X : C) :
    e.hom.app X = a.hom.app X ≫ b.hom.app X ≫ c.inv.app X :=
  (congrArg (fun z => z.hom.app X) h).trans (natural_transition_hom_app a b c X)

/-- The component equation of a specified three-step natural transition. -/
def HasTransitionComponents {F G H J : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : J ≅ H) (e : F ≅ J) (X : C) : Prop :=
  e.hom.app X = a.hom.app X ≫ b.hom.app X ≫ c.inv.app X

theorem hasTransitionComponents {F G H J : C ⥤ D}
    (a : F ≅ G) (b : G ≅ H) (c : J ≅ H) (e : F ≅ J)
    (h : e = a ≪≫ b ≪≫ c.symm) (X : C) : HasTransitionComponents a b c e X :=
  natural_transition_hom_of_eq a b c e h X

/-- Reverse an isomorphism in a commuting comparison square. -/
theorem reverse_square (F : C ⥤ D) {X Y : C} {P Q : D}
    (a : X ≅ Y) (u : F.obj X ≅ P) (v : F.obj Y ≅ Q) (g : P ≅ Q)
    (h : F.map a.inv ≫ u.hom = v.hom ≫ g.inv) :
    F.map a.hom ≫ v.hom = u.hom ≫ g.hom := by
  calc
    _ = F.map a.hom ≫ (v.hom ≫ g.inv) ≫ g.hom := by
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = F.map a.hom ≫ (F.map a.inv ≫ u.hom) ≫ g.hom := by rw [h]
    _ = _ := by
      have hm : F.map a.hom ≫ F.map a.inv = 𝟙 _ := by
        rw [← F.map_comp, a.hom_inv_id, F.map_id]
      simp only [← Category.assoc, hm, Category.id_comp]

/-- A three-step module transition is carried to its three geometric comparison maps. -/
theorem compose_squares (F : C ⥤ D) {X Y Z W : C} {P Q V T : D}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ W)
    (u : F.obj X ≅ P) (v : F.obj Y ≅ Q) (w : F.obj Z ≅ V) (t : F.obj W ≅ T)
    (g : P ≅ Q) (h : Q ≅ V) (k : T ≅ V)
    (ha : F.map a.hom ≫ v.hom = u.hom ≫ g.hom)
    (hb : F.map b.hom ≫ w.hom = v.hom ≫ h.hom)
    (hc : F.map c.inv ≫ w.hom = t.hom ≫ k.hom) :
    F.map (a.hom ≫ b.hom ≫ c.hom) ≫ t.hom =
      u.hom ≫ g.hom ≫ h.hom ≫ k.inv := by
  have hc' := reverse_square F c w t k.symm hc
  rw [F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [hc']
  rw [← Category.assoc (F.map b.hom), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map a.hom) v.hom, ha]
  simp only [Category.assoc, Iso.symm_hom]

/-- The same calculation on explicit component maps, retaining their specified inverse equations. -/
theorem compose_reversed_maps (F : C ⥤ D) {X Y Z W : C} {P Q V T : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ Z) (d : Z ⟶ W)
    (u : F.obj X ⟶ P) (v : F.obj Y ⟶ Q) (w : F.obj Z ⟶ V) (t : F.obj W ⟶ T)
    (g : P ⟶ Q) (h : Q ⟶ V) (k : T ⟶ V) (l : V ⟶ T)
    (ha : F.map a ≫ v = u ≫ g) (hb : F.map b ≫ w = v ≫ h)
    (hc : F.map c ≫ w = t ≫ k) (hd : d ≫ c = 𝟙 Z) (hk : k ≫ l = 𝟙 T) :
    F.map (a ≫ b ≫ d) ≫ t = u ≫ g ≫ h ≫ l := by
  have hc' : F.map d ≫ t = w ≫ l := by
    calc
      _ = F.map d ≫ (t ≫ k) ≫ l := by
        simp only [Category.assoc, hk, Category.comp_id]
      _ = F.map d ≫ (F.map c ≫ w) ≫ l := by rw [hc]
      _ = _ := by
        have hm : F.map d ≫ F.map c = 𝟙 _ := by rw [← F.map_comp, hd, F.map_id]
        simp only [← Category.assoc, hm, Category.id_comp]
  rw [F.map_comp, F.map_comp]
  simp only [Category.assoc]
  rw [hc']
  rw [← Category.assoc (F.map b), hb]
  simp only [Category.assoc]
  rw [← Category.assoc (F.map a) v, ha]
  simp only [Category.assoc]

/-- A comparison square, with its endpoint objects retained abstractly. -/
def IsSquare (F : C ⥤ D) {X Y : C} {P Q : D}
    (a : X ⟶ Y) (u : F.obj X ⟶ P) (v : F.obj Y ⟶ Q) (b : P ⟶ Q) : Prop :=
  F.map a ≫ v = u ≫ b

/-- A three-step comparison square before recognizing the composite transitions. -/
def IsTransitionSquare (F : C ⥤ D) {X Y Z W : C} {P Q V T : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (d : Z ⟶ W)
    (u : F.obj X ⟶ P) (t : F.obj W ⟶ T) (g : P ⟶ Q) (h : Q ⟶ V) (l : V ⟶ T) : Prop :=
  F.map (a ≫ b ≫ d) ≫ t = u ≫ g ≫ h ≫ l

theorem transitionSquare_of_reversed (F : C ⥤ D) {X Y Z W : C} {P Q V T : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : W ⟶ Z) (d : Z ⟶ W)
    (u : F.obj X ⟶ P) (v : F.obj Y ⟶ Q) (w : F.obj Z ⟶ V) (t : F.obj W ⟶ T)
    (g : P ⟶ Q) (h : Q ⟶ V) (k : T ⟶ V) (l : V ⟶ T)
    (ha : F.map a ≫ v = u ≫ g) (hb : F.map b ≫ w = v ≫ h)
    (hc : F.map c ≫ w = t ≫ k) (hd : d ≫ c = 𝟙 Z) (hk : k ≫ l = 𝟙 T) :
    IsTransitionSquare F a b d u t g h l :=
  compose_reversed_maps F a b c d u v w t g h k l ha hb hc hd hk

/-- Recognize both composites in a comparison square using their proved transition equations. -/
theorem finish_natural_transition_square {B : Type*} [Category B]
    (F : C ⥤ D) {X Y Z W : C} {G₀ G₁ G₂ G₃ : B ⥤ D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (d : Z ⟶ W) (e : X ≅ W)
    (α : G₀ ≅ G₁) (β : G₁ ≅ G₂) (γ : G₃ ≅ G₂) (η : G₀ ≅ G₃) (K : B)
    (u : F.obj X ⟶ G₀.obj K) (t : F.obj W ⟶ G₃.obj K)
    (hm : e.hom = a ≫ b ≫ d)
    (ht : IsTransitionSquare F a b d u t (α.hom.app K) (β.hom.app K) (γ.inv.app K))
    (hg : HasTransitionComponents α β γ η K) :
    IsSquare F e.hom u t (η.hom.app K) :=
  (congrArg (fun z => F.map z ≫ t) hm).trans
    (ht.trans (congrArg (fun z => u ≫ z) hg.symm))

/-- Compose comparison squares at the level of their whole isomorphisms. -/
theorem compose_iso_squares (F : C ⥤ D) {X Y Z W : C} {P Q V T : D}
    (a : X ≅ Y) (b : Y ≅ Z) (c : Z ≅ W)
    (u : F.obj X ≅ P) (v : F.obj Y ≅ Q) (w : F.obj Z ≅ V) (t : F.obj W ≅ T)
    (g : P ≅ Q) (h : Q ≅ V) (k : T ≅ V)
    (ha : F.mapIso a ≪≫ v = u ≪≫ g) (hb : F.mapIso b ≪≫ w = v ≪≫ h)
    (hc : F.mapIso c.symm ≪≫ w = t ≪≫ k) :
    F.mapIso (a ≪≫ b ≪≫ c) ≪≫ t = u ≪≫ g ≪≫ h ≪≫ k.symm := by
  apply Iso.ext
  exact compose_squares F a b c u v w t g h k
    (congrArg Iso.hom ha) (congrArg Iso.hom hb) (congrArg Iso.hom hc)

theorem natural_symm_app {F G : C ⥤ D} (e : F ≅ G) (X : C) :
    e.symm.app X = (e.app X).symm := rfl

/-- Recognize the two whole transitions in a comparison of isomorphisms. -/
theorem finish_iso_square (F : C ⥤ D) {X Y : C} {P Q : D}
    (a b : X ≅ Y) (u : F.obj X ≅ P) (v : F.obj Y ≅ Q) (c d : P ≅ Q)
    (ha : a = b) (hc : c = d) (h : F.mapIso b ≪≫ v = u ≪≫ d) :
    F.mapIso a ≪≫ v = u ≪≫ c :=
  (congrArg (fun z => F.mapIso z ≪≫ v) ha).trans
    (h.trans (congrArg (fun z => u ≪≫ z) hc.symm))

theorem natural_square_of_iso_square {B : Type*} [Category B]
    (F : C ⥤ D) {X Y : C} {G H : B ⥤ D} (e : X ≅ Y) (η : G ≅ H) (K : B)
    (u : F.obj X ≅ G.obj K) (v : F.obj Y ≅ H.obj K)
    (h : F.mapIso e ≪≫ v = u ≪≫ η.app K) :
    IsSquare F e.hom u.hom v.hom (η.hom.app K) := congrArg Iso.hom h

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.TransitionSquares
