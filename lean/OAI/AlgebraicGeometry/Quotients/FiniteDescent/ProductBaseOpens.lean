import OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseAxes
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Product Base Opens -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseOpens

noncomputable section

/-! Affine rectangles and the open sets on the two axes commute with
the actual product base-change maps. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

namespace Construction.ProductBaseChangeOpens

variable {X Y S X' Y' T : Scheme.{u}}
variable (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ T) (g' : Y' ⟶ T)
variable (p : X' ⟶ X) (q : Y' ⟶ Y) (t : T ⟶ S)
variable (hp : IsPullback p f' f t) (hq : IsPullback q g' g t)

theorem rectangle (U : X.Opens) (V : Y.Opens) :
    ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq ⁻¹ᵁ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) =
    pullback.fst f' g' ⁻¹ᵁ (p ⁻¹ᵁ U) ⊓ pullback.snd f' g' ⁻¹ᵁ (q ⁻¹ᵁ V) := by
  have he₁ : ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq ≫ pullback.fst f g =
      pullback.fst f' g' ≫ p := by
    exact pullback.lift_fst _ _ _
  have he₂ : ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq ≫ pullback.snd f g =
      pullback.snd f' g' ≫ q := by
    exact pullback.lift_snd _ _ _
  change (ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq ≫ pullback.fst f g) ⁻¹ᵁ U ⊓
    (ProductBaseLift.Construction.ProductBaseChangeSquare.map f g f' g' p q t hp hq ≫ pullback.snd f g) ⁻¹ᵁ V = _
  rw [he₁, he₂]
  rfl

omit hp hq in
theorem left (s : S ⟶ Y) (hs : s ≫ g = 𝟙 _) (U : X.Opens) (V : Y.Opens)
    (hV : ⊤ ≤ s ⁻¹ᵁ V) : U ≤ ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g s hs ⁻¹ᵁ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have he₁ : ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g s hs ≫ pullback.fst f g = 𝟙 X :=
    pullback.lift_fst _ _ _
  have he₂ : ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g s hs ≫ pullback.snd f g = f ≫ s :=
    pullback.lift_snd _ _ _
  change U ≤ (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g s hs ≫ pullback.fst f g) ⁻¹ᵁ U ⊓
    (ProductBaseAxes.Construction.ProductBaseChangeAxes.left f g s hs ≫ pullback.snd f g) ⁻¹ᵁ V
  rw [he₁, he₂]
  intro x hx
  exact ⟨hx, hV (show f x ∈ (⊤ : S.Opens) from trivial)⟩

omit hp hq in
theorem right (s : S ⟶ X) (hs : s ≫ f = 𝟙 _) (U : X.Opens) (V : Y.Opens)
    (hU : ⊤ ≤ s ⁻¹ᵁ U) : V ≤ ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g s hs ⁻¹ᵁ
      (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have he₁ : ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g s hs ≫ pullback.fst f g = g ≫ s :=
    pullback.lift_fst _ _ _
  have he₂ : ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g s hs ≫ pullback.snd f g = 𝟙 Y :=
    pullback.lift_snd _ _ _
  change V ≤ (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g s hs ≫ pullback.fst f g) ⁻¹ᵁ U ⊓
    (ProductBaseAxes.Construction.ProductBaseChangeAxes.right f g s hs ≫ pullback.snd f g) ⁻¹ᵁ V
  rw [he₁, he₂]
  intro y hy
  exact ⟨hU (show g y ∈ (⊤ : S.Opens) from trivial), hy⟩

end Construction.ProductBaseChangeOpens

end

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.ProductBaseOpens
