import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift

/-! # Product Base Axes -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes

noncomputable section

/-! Rational-point axes and their Cartesian base-change squares. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X Y S X' Y' T : C}

def left (f : X ⟶ S) (g : Y ⟶ S) (s : S ⟶ Y) (hs : s ≫ g = 𝟙 _) : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) (f ≫ s) (by simp [Category.assoc, hs])

theorem left_over (f : X ⟶ S) (g : Y ⟶ S) (s : S ⟶ Y) (hs : s ≫ g = 𝟙 _) :
    left f g s hs ≫ (pullback.fst f g ≫ f) = f := by
  rw [left, pullback.lift_fst_assoc, Category.id_comp]

def baseSection (f : X ⟶ S) (f' : X' ⟶ T) (p : X' ⟶ X) (t : T ⟶ S)
    (hp : IsPullback p f' f t) (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) : T ⟶ X' :=
  hp.lift (t ≫ s) (𝟙 T) (by simp [Category.assoc, hs])

omit [HasPullbacks C] in
theorem section_over (f : X ⟶ S) (f' : X' ⟶ T) (p : X' ⟶ X) (t : T ⟶ S)
    (hp : IsPullback p f' f t) (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) :
    baseSection f f' p t hp s hs ≫ f' = 𝟙 T := hp.lift_snd _ _ _

variable (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ T) (g' : Y' ⟶ T)
variable (p : X' ⟶ X) (q : Y' ⟶ Y) (t : T ⟶ S)
variable (hp : IsPullback p f' f t) (hq : IsPullback q g' g t)
variable (s : S ⟶ Y) (hs : s ≫ g = 𝟙 _)

abbrev liftedLeft := left f' g' (baseSection g g' q t hq s hs) (section_over g g' q t hq s hs)

theorem left_square :
    liftedLeft g f' g' q t hq s hs ≫ ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq =
      p ≫ left f g s hs := by
  apply pullback.hom_ext
  · simp only [liftedLeft, left, ProductBaseLift.Construction.ProductBaseChangeSquare.map, pullback.map,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
  · simp only [liftedLeft, left, ProductBaseLift.Construction.ProductBaseChangeSquare.map, pullback.map,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, baseSection, IsPullback.lift_fst]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ s) hp.w.symm

theorem left_isPullback :
    IsPullback (liftedLeft g f' g' q t hq s hs) p
      (ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq) (left f g s hs) := by
  have ho : IsPullback
      (liftedLeft g f' g' q t hq s hs ≫ (pullback.fst f' g' ≫ f')) p t
      (left f g s hs ≫ (pullback.fst f g ≫ f)) := by
    rw [left_over, left_over]
    exact hp.flip
  exact IsPullback.of_right ho (left_square f g f' g' p q t hp hq s hs)
    (ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p q t hp hq).flip

def right (f : X ⟶ S) (g : Y ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) : Y ⟶ pullback f g :=
  pullback.lift (g ≫ s) (𝟙 Y) (by simp [Category.assoc, hs])

theorem right_over (f : X ⟶ S) (g : Y ⟶ S) (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) :
    right f g s hs ≫ (pullback.fst f g ≫ f) = g := by
  rw [right, pullback.lift_fst_assoc, Category.assoc, hs, Category.comp_id]

variable (sX : S ⟶ X) (hsX : sX ≫ f = 𝟙 _)

abbrev liftedRight := right f' g' (baseSection f f' p t hp sX hsX) (section_over f f' p t hp sX hsX)

theorem right_square :
    liftedRight f f' g' p t hp sX hsX ≫ ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq =
      q ≫ right f g sX hsX := by
  apply pullback.hom_ext
  · simp only [liftedRight, right, ProductBaseLift.Construction.ProductBaseChangeSquare.map, pullback.map,
      Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, baseSection, IsPullback.lift_fst]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ sX) hq.w.symm
  · simp only [liftedRight, right, ProductBaseLift.Construction.ProductBaseChangeSquare.map, pullback.map,
      Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]

theorem right_isPullback :
    IsPullback (liftedRight f f' g' p t hp sX hsX) q
      (ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq) (right f g sX hsX) := by
  have ho : IsPullback
      (liftedRight f f' g' p t hp sX hsX ≫ (pullback.fst f' g' ≫ f')) q t
      (right f g sX hsX ≫ (pullback.fst f g ≫ f)) := by
    rw [right_over, right_over]
    exact hq.flip
  exact IsPullback.of_right ho (right_square f g f' g' p q t hp hq sX hsX)
    (ProductBaseLift.Construction.ProductBaseChangeSquare.isPullback f g f' g' p q t hp hq).flip

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes.Construction.ProductBaseChangeAxes
