import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.RingSquare
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence

/-! # Frame Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FrameSquare.BoundedGeometricFrameSquare

noncomputable section

/-! The actual geometric frame square is determined by its unchanged
divided-power ring maps under postcomposition. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X Y : Scheme.{u}} {fX : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  (g : X ⟶ Y) (hg : g ≫ fY = fX) (n : ℕ)
  {U V : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fX n}
  {U' V' : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n}
  (a : U ⟶ V) (b : U' ⟶ V')
  (c : (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj U ⟶ U')
  (d : (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).obj V ⟶ V')

theorem square (h : a.hom.ringMap.toRingHom.comp d.hom.ringMap.toRingHom =
    c.hom.ringMap.toRingHom.comp b.hom.ringMap.toRingHom) :
    (IntegralComparison.BoundedOpen.Equivalence.postcompose g hg n).map a ≫ d = c ≫ b :=
  BoundedFrame.RingSquare.BoundedFrameRingSquare.square_ringHom _ _ _ _ h

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FrameSquare.BoundedGeometricFrameSquare
