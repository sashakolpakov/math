import OAI.ArithmeticGeometry.Models.OpenPushout
import OAI.ArithmeticGeometry.Models.FoundationsPullback

/-! # Gluing Base Change -/

namespace OAI.ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations

/-! Gluing two open pieces commutes with a change of base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {S T : Scheme.{u}} (b : T ⟶ S)

noncomputable def baseChangeChart {A : Over T} {A₀ B₀ : Over S}
    (i : A₀ ⟶ B₀) (p : A.left ⟶ A₀.left) (hp : p ≫ A₀.hom = A.hom ≫ b) :
    A.left ⟶ ((Over.pullback b).obj B₀).left :=
  pullback.lift (p ≫ i.left) A.hom (by rw [Category.assoc, i.w, hp])

@[reassoc (attr := simp)]
theorem baseChangeChart_fst {A : Over T} {A₀ B₀ : Over S}
    (i : A₀ ⟶ B₀) (p : A.left ⟶ A₀.left) (hp : p ≫ A₀.hom = A.hom ≫ b) :
    baseChangeChart b i p hp ≫ pullback.fst B₀.hom b = p ≫ i.left :=
  pullback.lift_fst ..

@[reassoc (attr := simp)]
theorem baseChangeChart_snd {A : Over T} {A₀ B₀ : Over S}
    (i : A₀ ⟶ B₀) (p : A.left ⟶ A₀.left) (hp : p ≫ A₀.hom = A.hom ≫ b) :
    baseChangeChart b i p hp ≫ pullback.snd B₀.hom b = A.hom :=
  pullback.lift_snd ..

theorem baseChangeChart_cartesian {A : Over T} {A₀ B₀ : Over S}
    (i : A₀ ⟶ B₀) (p : A.left ⟶ A₀.left) (hp : IsPullback p A.hom A₀.hom b) :
    IsPullback p (baseChangeChart b i p hp.w) i.left (pullback.fst B₀.hom b) := by
  apply IsPullback.of_bot ?_ (baseChangeChart_fst b i p hp.w).symm
    (IsPullback.of_hasPullback B₀.hom b)
  rw [baseChangeChart_snd, i.w]
  exact hp

theorem baseChangeChart_compatible {W X Y : Over T} {W₀ X₀ Y₀ P₀ : Over S}
    (f : W ⟶ X) (g : W ⟶ Y) (f₀ : W₀ ⟶ X₀) (g₀ : W₀ ⟶ Y₀)
    (i : X₀ ⟶ P₀) (j : Y₀ ⟶ P₀) (hij : f₀.left ≫ i.left = g₀.left ≫ j.left)
    (pW : W.left ⟶ W₀.left) (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hX : pX ≫ X₀.hom = X.hom ≫ b) (hY : pY ≫ Y₀.hom = Y.hom ≫ b)
    (hf : f.left ≫ pX = pW ≫ f₀.left) (hg : g.left ≫ pY = pW ≫ g₀.left) :
    f.left ≫ baseChangeChart b i pX hX = g.left ≫ baseChangeChart b j pY hY := by
  apply pullback.hom_ext
  · rw [Category.assoc, baseChangeChart_fst, Category.assoc, baseChangeChart_fst,
      ← Category.assoc, hf, Category.assoc, hij, ← Category.assoc, ← hg, Category.assoc]
  · rw [Category.assoc, baseChangeChart_snd, Category.assoc, baseChangeChart_snd, f.w, g.w]

noncomputable def openGluedOver {W₀ X₀ Y₀ : Over S} (f₀ : W₀ ⟶ X₀) (g₀ : W₀ ⟶ Y₀)
    [IsOpenImmersion f₀.left] [IsOpenImmersion g₀.left] : Over S :=
  Over.mk (pushout.desc X₀.hom Y₀.hom (f₀.w.trans g₀.w.symm))

noncomputable def openGluedInl {W₀ X₀ Y₀ : Over S} (f₀ : W₀ ⟶ X₀) (g₀ : W₀ ⟶ Y₀)
    [IsOpenImmersion f₀.left] [IsOpenImmersion g₀.left] : X₀ ⟶ openGluedOver f₀ g₀ :=
  Over.homMk (pushout.inl f₀.left g₀.left) (pushout.inl_desc ..)

noncomputable def openGluedInr {W₀ X₀ Y₀ : Over S} (f₀ : W₀ ⟶ X₀) (g₀ : W₀ ⟶ Y₀)
    [IsOpenImmersion f₀.left] [IsOpenImmersion g₀.left] : Y₀ ⟶ openGluedOver f₀ g₀ :=
  Over.homMk (pushout.inr f₀.left g₀.left) (pushout.inr_desc ..)

theorem openGluedBaseChange_isPushout
    {W X Y : Over T} {W₀ X₀ Y₀ : Over S}
    (f : W ⟶ X) (g : W ⟶ Y) (f₀ : W₀ ⟶ X₀) (g₀ : W₀ ⟶ Y₀)
    [IsOpenImmersion f₀.left] [IsOpenImmersion g₀.left]
    (pW : W.left ⟶ W₀.left) (pX : X.left ⟶ X₀.left) (pY : Y.left ⟶ Y₀.left)
    (hW : IsPullback pW W.hom W₀.hom b)
    (hX : IsPullback pX X.hom X₀.hom b)
    (hY : IsPullback pY Y.hom Y₀.hom b)
    (hf : f.left ≫ pX = pW ≫ f₀.left) (hg : g.left ≫ pY = pW ≫ g₀.left) :
    IsPushout f.left g.left
      (baseChangeChart b (openGluedInl f₀ g₀) pX hX.w)
      (baseChangeChart b (openGluedInr f₀ g₀) pY hY.w) := by
  let P₀ := openGluedOver f₀ g₀
  let i := openGluedInl f₀ g₀
  let j := openGluedInr f₀ g₀
  let l := baseChangeChart b i pX hX.w
  let r := baseChangeChart b j pY hY.w
  have hi : IsPullback pX l i.left (pullback.fst P₀.hom b) :=
    baseChangeChart_cartesian b i pX hX
  have hj : IsPullback pY r j.left (pullback.fst P₀.hom b) :=
    baseChangeChart_cartesian b j pY hY
  let : IsOpenImmersion i.left := OpenPushout.Constructions.Foundations.openPushout_inl_open f₀.left g₀.left
  let : IsOpenImmersion j.left := OpenPushout.Constructions.Foundations.openPushout_inr_open f₀.left g₀.left
  let : IsOpenImmersion l := MorphismProperty.IsStableUnderBaseChange.of_isPullback hi inferInstance
  let : IsOpenImmersion r := MorphismProperty.IsStableUnderBaseChange.of_isPullback hj inferInstance
  have hcov (z : ((Over.pullback b).obj P₀).left) :
      (∃ x, l x = z) ∨ (∃ y, r y = z) := by
    rcases OpenPushout.Constructions.Foundations.openPushout_covers f₀.left g₀.left (pullback.fst P₀.hom b z) with ⟨x, hx⟩ | ⟨y, hy⟩
    · obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback hi x z hx
      exact Or.inl ⟨a, ha⟩
    · obtain ⟨a, _, ha⟩ := Scheme.exists_preimage_of_isPullback hj y z hy
      exact Or.inr ⟨a, ha⟩
  have hcomm : f.left ≫ l = g.left ≫ r :=
    baseChangeChart_compatible b f g f₀ g₀ i j (pushout.condition (f := f₀.left) (g := g₀.left))
      pW pX pY hX.w hY.w hf hg
  have hWY : IsPullback pW g.left g₀.left pY := by
    apply IsPullback.of_bot ?_ hg.symm hY
    rw [g.w, g₀.w]
    exact hW
  have hInt : IsPullback f₀.left g₀.left i.left j.left :=
    OpenPushout.Constructions.Foundations.openPushout_isPullback f₀.left g₀.left
  have hOuter : IsPullback (f.left ≫ pX) g.left i.left (r ≫ pullback.fst P₀.hom b) := by
    rw [hf, baseChangeChart_fst]
    exact hWY.paste_horiz hInt
  exact OpenPushout.Constructions.Foundations.openPair_isPushout f.left g.left l r hcov (hOuter.of_right hcomm hi)

end OAI.ArithmeticGeometry.Models.GluingBaseChange.Constructions.Foundations
