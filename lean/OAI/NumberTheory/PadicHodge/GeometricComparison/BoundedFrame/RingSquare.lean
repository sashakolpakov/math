import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingExt

/-! # Ring Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingSquare.BoundedFrameRingSquare

noncomputable section

/-! Generator formulas prove a commuting square of bounded crystalline frames. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u v
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of B)} {n : ℕ}
  {U V U' V' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n}
  {A₁ A₂ : Type v}

theorem ringHom {a b : U ⟶ V} (h : a.hom.ringMap.toRingHom = b.hom.ringMap.toRingHom) : a = b :=
  RingExt.BoundedFrameRingExt.ext_fun (fun x => RingHom.congr_fun h x)

theorem comp_ringHom (a : U ⟶ V) (b : V ⟶ V') :
    (a ≫ b).hom.ringMap.toRingHom = a.hom.ringMap.toRingHom.comp b.hom.ringMap.toRingHom := rfl

theorem square_ringHom (a : U ⟶ V) (b : U' ⟶ V') (c : U ⟶ U') (d : V ⟶ V')
    (h : a.hom.ringMap.toRingHom.comp d.hom.ringMap.toRingHom =
      c.hom.ringMap.toRingHom.comp b.hom.ringMap.toRingHom) : a ≫ d = c ≫ b := ringHom h

theorem square (qU : A₁ → U.obj.ring) (qV : A₂ → V.obj.ring)
    (qU' : A₁ → U'.obj.ring) (qV' : A₂ → V'.obj.ring)
    (hq : Function.Surjective qV') (r : A₂ → A₁)
    (a : U ⟶ V) (b : U' ⟶ V') (c : U ⟶ U') (d : V ⟶ V')
    (ha : ∀ x, a.hom.ringMap (qV x) = qU (r x))
    (hb : ∀ x, b.hom.ringMap (qV' x) = qU' (r x))
    (hc : ∀ x, c.hom.ringMap (qU' x) = qU x)
    (hd : ∀ x, d.hom.ringMap (qV' x) = qV x) : a ≫ d = c ≫ b := by
  apply RingExt.BoundedFrameRingExt.ext_fun
  intro y
  obtain ⟨x, rfl⟩ := hq y
  exact (congrArg a.hom.ringMap (hd x)).trans
    ((ha x).trans ((hc (r x)).symm.trans (congrArg c.hom.ringMap (hb x)).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingSquare.BoundedFrameRingSquare
