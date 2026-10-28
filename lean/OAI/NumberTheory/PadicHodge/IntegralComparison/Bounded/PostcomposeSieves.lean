import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Postcompose Sieves -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeSieves

noncomputable section

/-!
# IntegralComparison: sieve comparison for actual bounded crystalline postcomposition
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)

local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "F" => OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite.postcompose (p := p) (J := J) (δ := δ) g hg
local notation "F₀" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n

variable {U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}

theorem pushforward_comp (S : Sieve U) :
    (S.functorPushforward F₀).functorPushforward QY = (S.functorPushforward QX).functorPushforward F :=
  (Sieve.functorPushforward_comp F₀ QY S).symm.trans (Sieve.functorPushforward_comp QX F S)

theorem pushforward_pullback (S : Sieve ((F₀).obj U)) :
    (S.functorPullback F₀).functorPushforward QX = (S.functorPushforward QY).functorPullback F := by
  apply le_antisymm
  · intro V α hα
    obtain ⟨W, β, γ, hβ, rfl⟩ := hα
    change (S.functorPushforward QY) ((F).map (γ ≫ (QX).map β))
    rw [Functor.map_comp]
    exact (S.functorPushforward QY).downward_closed
      (Sieve.image_mem_functorPushforward QY S (f := (F₀).map β) hβ) ((F).map γ)
  · intro V α hα
    let V₀ : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n :=
      ⟨V, BoundedCrystalline.Site.property_of_hom f n α U.property⟩
    let β : V₀ ⟶ U := ObjectProperty.homMk α
    have hβ : S ((F₀).map β) :=
      (Sieve.mem_functorPushforward_iff_of_full_of_faithful QY S ((F₀).map β)).mp hα
    exact ⟨V₀, β, 𝟙 V, hβ, Category.id_comp α⟩

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.PostcomposeSieves
