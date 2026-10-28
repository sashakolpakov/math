import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
import Mathlib.RingTheory.RingHom.Flat

/-! # Base Ring -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.BaseRing

noncomputable section

/-! The original coefficient ring acts on every bounded frame through its native prime-power quotient. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n : ℕ)

theorem kills (U : Site.Objects (p := p) (J := J) (δ := δ) f n) :
    (Ideal.span {(p : B)}) ^ (n + 1) ≤ RingHom.ker U.obj.base := by
  rw [Ideal.span_singleton_pow, Ideal.span_le]
  rintro a (rfl : a = _)
  change U.obj.base ((p : B) ^ (n + 1)) = 0
  rw [map_pow, map_natCast]
  exact U.property

def base (U : Site.Objects (p := p) (J := J) (δ := δ) f n) :
    (B ⧸ (Ideal.span {(p : B)}) ^ (n + 1)) →+* U.obj.ring :=
  Ideal.Quotient.lift _ U.obj.base (kills f n U)

theorem base_mk (U : Site.Objects (p := p) (J := J) (δ := δ) f n) (b : B) :
    BaseRing.base f n U (Ideal.Quotient.mk ((Ideal.span {(p : B)}) ^ (n + 1)) b) = U.obj.base b := rfl

theorem natural {U V : Site.Objects (p := p) (J := J) (δ := δ) f n} (α : U ⟶ V) :
    α.hom.ringMap.toRingHom.comp (BaseRing.base f n V) = BaseRing.base f n U := by
  apply RingHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact DFunLike.congr_fun α.hom.overBase b

theorem flat_of_hom {U V : Site.Objects (p := p) (J := J) (δ := δ) f n} (α : U ⟶ V)
    (hα : α.hom.ringMap.toRingHom.Flat) (hV : (BaseRing.base f n V).Flat) : (BaseRing.base f n U).Flat :=
  natural f n α ▸ hV.comp hα

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.BaseRing
