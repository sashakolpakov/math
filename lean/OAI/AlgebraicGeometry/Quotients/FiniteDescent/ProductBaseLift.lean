import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Product Base Lift -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare

noncomputable section

/-! The product of two base-change squares is itself a base-change square. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {X Y S X' Y' T : C}
variable (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ T) (g' : Y' ⟶ T)
variable (p : X' ⟶ X) (q : Y' ⟶ Y) (t : T ⟶ S)
variable (hp : IsPullback p f' f t) (hq : IsPullback q g' g t)

def map : pullback f' g' ⟶ pullback f g :=
  pullback.map f' g' f g p q t hp.w.symm hq.w.symm

theorem condition : ProductBaseChangeSquare.map f g f' g' p q t hp hq ≫ (pullback.fst f g ≫ f) =
    (pullback.fst f' g' ≫ f') ≫ t := by
  simp only [ProductBaseChangeSquare.map, pullback.map, Category.assoc, pullback.lift_fst_assoc, hp.w]

def lift (s : PullbackCone (pullback.fst f g ≫ f) t) : s.pt ⟶ pullback f' g' := by
  let a := hp.lift (s.fst ≫ pullback.fst f g) s.snd
    (by simpa only [Category.assoc] using s.condition)
  have hb : (s.fst ≫ pullback.snd f g) ≫ g = s.snd ≫ t := by
    rw [Category.assoc, ← pullback.condition]
    exact s.condition
  let b := hq.lift (s.fst ≫ pullback.snd f g) s.snd hb
  exact pullback.lift a b (by simp [a, b])

theorem lift_map (s : PullbackCone (pullback.fst f g ≫ f) t) :
    ProductBaseChangeSquare.lift f g f' g' p q t hp hq s ≫ ProductBaseChangeSquare.map f g f' g' p q t hp hq = s.fst := by
  apply pullback.hom_ext
  · dsimp only [ProductBaseChangeSquare.lift, ProductBaseChangeSquare.map, pullback.map]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, IsPullback.lift_fst]
  · dsimp only [ProductBaseChangeSquare.lift, ProductBaseChangeSquare.map, pullback.map]
    simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, IsPullback.lift_fst]

theorem lift_base (s : PullbackCone (pullback.fst f g ≫ f) t) :
    ProductBaseChangeSquare.lift f g f' g' p q t hp hq s ≫ (pullback.fst f' g' ≫ f') = s.snd := by
  dsimp only [ProductBaseChangeSquare.lift]
  simp only [pullback.lift_fst_assoc, IsPullback.lift_snd]

theorem unique (s : PullbackCone (pullback.fst f g ≫ f) t) (a b : s.pt ⟶ pullback f' g')
    (ha : a ≫ ProductBaseChangeSquare.map f g f' g' p q t hp hq = b ≫ ProductBaseChangeSquare.map f g f' g' p q t hp hq)
    (hb : a ≫ (pullback.fst f' g' ≫ f') = b ≫ (pullback.fst f' g' ≫ f')) : a = b := by
  apply pullback.hom_ext
  · apply hp.hom_ext
    · have he := congrArg (fun z => z ≫ pullback.fst f g) ha
      simpa only [ProductBaseChangeSquare.map, pullback.map, Category.assoc, pullback.lift_fst] using he
    · simpa only [Category.assoc] using hb
  · apply hq.hom_ext
    · have he := congrArg (fun z => z ≫ pullback.snd f g) ha
      simpa only [ProductBaseChangeSquare.map, pullback.map, Category.assoc, pullback.lift_snd] using he
    · simpa only [Category.assoc, pullback.condition] using hb

theorem isPullback : IsPullback (ProductBaseChangeSquare.map f g f' g' p q t hp hq)
    (pullback.fst f' g' ≫ f') (pullback.fst f g ≫ f) t := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ (ProductBaseChangeSquare.condition f g f' g' p q t hp hq))
  apply PullbackCone.isLimitAux' (PullbackCone.mk _ _ (ProductBaseChangeSquare.condition f g f' g' p q t hp hq))
  intro s
  refine ⟨ProductBaseChangeSquare.lift f g f' g' p q t hp hq s, lift_map f g f' g' p q t hp hq s,
    lift_base f g f' g' p q t hp hq s, ?_⟩
  intro m hm₁ hm₂
  exact unique f g f' g' p q t hp hq s m _
    (hm₁.trans (lift_map f g f' g' p q t hp hq s).symm)
    (hm₂.trans (lift_base f g f' g' p q t hp hq s).symm)

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseLift.Construction.ProductBaseChangeSquare
