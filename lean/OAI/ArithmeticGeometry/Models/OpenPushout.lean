import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Cover.Directed

/-! # Open Pushout -/

namespace OAI.ArithmeticGeometry.Models.OpenPushout.Constructions.Foundations

/-! Binary gluing along open subschemes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {W X Y : Scheme.{u}} (f : W ⟶ X) (g : W ⟶ Y)
  [IsOpenImmersion f] [IsOpenImmersion g]

theorem openPushout_inl_open : IsOpenImmersion (pushout.inl f g) := by
  change IsOpenImmersion (colimit.ι (span f g) (some WalkingPair.left))
  infer_instance

theorem openPushout_inr_open : IsOpenImmersion (pushout.inr f g) := by
  change IsOpenImmersion (colimit.ι (span f g) (some WalkingPair.right))
  infer_instance

theorem openPushout_covers (x : (pushout f g : Scheme)) :
    (∃ a, pushout.inl f g a = x) ∨ (∃ b, pushout.inr f g b = x) := by
  obtain ⟨i, y, hy⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) x
  cases i with
  | none =>
      left
      refine ⟨f y, ?_⟩
      erw [← Scheme.Hom.comp_apply]
      exact (congrArg (fun h : W ⟶ pushout f g ↦ h y)
        (colimit.w (span f g) (WidePushoutShape.Hom.init WalkingPair.left))).trans hy
  | some i =>
      cases i with
      | left => exact Or.inl ⟨y, hy⟩
      | right => exact Or.inr ⟨y, hy⟩

theorem openPushout_intersection (x : X) (y : Y) :
    pushout.inl f g x = pushout.inr f g y ↔ ∃ w, f w = x ∧ g w = y := by
  constructor
  · intro h
    obtain ⟨k, a, b, w, ha, hb⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)).mp h
    cases a with
    | id => cases b
    | init =>
      cases b with
      | init => exact ⟨w, ha, hb⟩
  · rintro ⟨w, rfl, rfl⟩
    simpa only [← Scheme.Hom.comp_apply] using
      congrArg (fun h : W ⟶ pushout f g ↦ h w) (pushout.condition (f := f) (g := g))

theorem openPushout_isPullback :
    IsPullback f g (pushout.inl f g) (pushout.inr f g) := by
  let : IsOpenImmersion (pushout.inl f g) := openPushout_inl_open f g
  let : IsOpenImmersion (pushout.inr f g) := openPushout_inr_open f g
  apply IsOpenImmersion.isPullback f g (pushout.inl f g) (pushout.inr f g)
    (pushout.condition (f := f) (g := g)).symm
  ext y
  change (∃ x, pushout.inl f g x = pushout.inr f g y) ↔ ∃ w, g w = y
  constructor
  · rintro ⟨x, h⟩
    obtain ⟨w, _, hw⟩ := (openPushout_intersection f g x y).mp h
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact ⟨f w, (openPushout_intersection f g _ _).mpr ⟨w, rfl, rfl⟩⟩

variable {P : Scheme.{u}} (i : X ⟶ P) (j : Y ⟶ P)
  [IsOpenImmersion i] [IsOpenImmersion j]
  (hc : ∀ p : P, (∃ x, i x = p) ∨ (∃ y, j y = p))

def openPairObj : Bool → Scheme.{u} | false => X | true => Y

def openPairMap : ∀ b, openPairObj (X := X) (Y := Y) b ⟶ P
  | false => i
  | true => j

noncomputable def openPairCover : P.OpenCover :=
  Scheme.Cover.mkOfCovers Bool openPairObj (openPairMap i j)
    (fun p ↦ by
      rcases hc p with ⟨x, hx⟩ | ⟨y, hy⟩
      · exact ⟨false, x, hx⟩
      · exact ⟨true, y, hy⟩)
    (fun b ↦ by cases b <;> assumption)

omit [IsOpenImmersion f] [IsOpenImmersion g] in
theorem pullback_compatible {Q : Scheme.{u}} {i : X ⟶ P} {j : Y ⟶ P}
    (h : IsPullback f g i j) (a : X ⟶ Q) (b : Y ⟶ Q) (hab : f ≫ a = g ≫ b) :
    pullback.fst i j ≫ a = pullback.snd i j ≫ b := by
  rw [← h.isoPullback_inv_fst, ← h.isoPullback_inv_snd, Category.assoc, Category.assoc, hab]

include hc in
omit [IsOpenImmersion f] [IsOpenImmersion g] in
theorem openPair_isPushout (h : IsPullback f g i j) : IsPushout f g i j := by
  let C := openPairCover i j hc
  have compat (s : PushoutCocone f g) : ∀ a b : Bool,
      pullback.fst (C.f a) (C.f b) ≫
          (show C.X a ⟶ s.pt from openPairMap s.inl s.inr a) =
        pullback.snd (C.f a) (C.f b) ≫
          (show C.X b ⟶ s.pt from openPairMap s.inl s.inr b) := by
    intro a b
    cases a <;> cases b
    · have he : pullback.fst i i = pullback.snd i i :=
        (cancel_mono i).mp pullback.condition
      change pullback.fst i i ≫ s.inl = pullback.snd i i ≫ s.inl
      rw [he]
    · exact pullback_compatible f g h s.inl s.inr s.condition
    · exact pullback_compatible g f h.flip s.inr s.inl s.condition.symm
    · have he : pullback.fst j j = pullback.snd j j :=
        (cancel_mono j).mp pullback.condition
      change pullback.fst j j ≫ s.inr = pullback.snd j j ≫ s.inr
      rw [he]
  let d (s : PushoutCocone f g) := C.glueMorphisms (openPairMap s.inl s.inr) (compat s)
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j h.w)
  refine PushoutCocone.IsColimit.mk h.w d ?_ ?_ ?_
  · intro s
    exact C.ι_glueMorphisms _ (compat s) false
  · intro s
    exact C.ι_glueMorphisms _ (compat s) true
  · intro s m hm₁ hm₂
    apply C.hom_ext
    intro b
    cases b
    · exact hm₁.trans (C.ι_glueMorphisms _ (compat s) false).symm
    · exact hm₂.trans (C.ι_glueMorphisms _ (compat s) true).symm

end OAI.ArithmeticGeometry.Models.OpenPushout.Constructions.Foundations
