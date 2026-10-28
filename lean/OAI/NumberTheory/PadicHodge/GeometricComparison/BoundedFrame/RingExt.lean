import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

/-! # Ring Ext -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingExt.BoundedFrameRingExt

noncomputable section

/-! Bounded frame maps are determined on any surjective family of ring elements. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u v
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {n : ℕ}
  {U V T : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}

theorem ext_fun {α β : U ⟶ V} (h : ∀ x, α.hom.ringMap x = β.hom.ringMap x) : α = β := by
  apply (IntegralComparison.BoundedCrystalline.Site.inclusion f n).map_injective
  apply IntegralComparison.BigCrystallineSite.Object.Hom.ext
  ext x
  exact h x

theorem id_of_surjective {A : Type v} (q : A → U.obj.ring) (hq : Function.Surjective q)
    (α : U ⟶ U) (h : ∀ a, α.hom.ringMap (q a) = q a) : α = 𝟙 U := by
  apply ext_fun
  intro x
  obtain ⟨a, rfl⟩ := hq x
  exact h a

theorem comp_of_surjective {A : Type v} (q : A → T.obj.ring) (hq : Function.Surjective q)
    (α : U ⟶ V) (β : V ⟶ T) (γ : U ⟶ T)
    (h : ∀ a, γ.hom.ringMap (q a) = α.hom.ringMap (β.hom.ringMap (q a))) :
    γ = α ≫ β := by
  apply ext_fun
  intro x
  obtain ⟨a, rfl⟩ := hq x
  exact h a

theorem id_of_formula {A : Type v} (q : A → U.obj.ring) (hq : Function.Surjective q)
    (α : U ⟶ U) (r : A → A) (h : ∀ a, α.hom.ringMap (q a) = q (r a))
    (hr : ∀ a, r a = a) : α = 𝟙 U :=
  id_of_surjective q hq α (fun a => (h a).trans (congrArg q (hr a)))

theorem comp_of_formulas {A₁ A₂ A₃ : Type v}
    (q₁ : A₁ → U.obj.ring) (q₂ : A₂ → V.obj.ring) (q₃ : A₃ → T.obj.ring)
    (hq₃ : Function.Surjective q₃)
    (α : U ⟶ V) (β : V ⟶ T) (γ : U ⟶ T)
    (r₁₂ : A₂ → A₁) (r₂₃ : A₃ → A₂) (r₁₃ : A₃ → A₁)
    (hα : ∀ a, α.hom.ringMap (q₂ a) = q₁ (r₁₂ a))
    (hβ : ∀ a, β.hom.ringMap (q₃ a) = q₂ (r₂₃ a))
    (hγ : ∀ a, γ.hom.ringMap (q₃ a) = q₁ (r₁₃ a))
    (hr : ∀ a, r₁₃ a = r₁₂ (r₂₃ a)) : γ = α ≫ β :=
  comp_of_surjective q₃ hq₃ α β γ (fun a =>
    (hγ a).trans ((congrArg q₁ (hr a)).trans
      ((congrArg α.hom.ringMap (hβ a)).trans (hα (r₂₃ a))).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingExt.BoundedFrameRingExt
