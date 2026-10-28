import OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameHomotopy

/-! # Frame Transport -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameTransport.Comparison

noncomputable section

/-! Comparison maps on equal geometric opens can be placed on the
same original incoming site before applying uniqueness of resolutions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (V V' : Y.Opens) (h : V = V')
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))

def map
    (b : FrameHomotopy.Comparison.complex f n V' F ⟶
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V'.ι n) I).cocomplex) :
    FrameHomotopy.Comparison.complex f n V F ⟶
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V.ι n) I).cocomplex := by
  subst V'
  exact b

theorem augmentation
    (b : FrameHomotopy.Comparison.complex f n V' F ⟶
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V'.ι n) I).cocomplex)
    (hb : FrameHomotopy.Comparison.augmentation f n V' F ≫ b =
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V'.ι n) I).ι) :
    FrameHomotopy.Comparison.augmentation f n V F ≫ map f n V V' h F I b =
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V.ι n) I).ι := by
  subst V'
  exact hb

variable (G : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) (a : G ⟶ F)

def homotopy [QuasiIso (FrameHomotopy.Comparison.augmentation f n V F)]
    (bF : FrameHomotopy.Comparison.complex f n V F ⟶
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V.ι n) I).cocomplex)
    (bG : FrameHomotopy.Comparison.complex f n V' G ⟶
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V'.ι n) I).cocomplex)
    (hF : FrameHomotopy.Comparison.augmentation f n V F ≫ bF =
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V.ι n) I).ι)
    (hG : FrameHomotopy.Comparison.augmentation f n V' G ≫ bG =
      (ExactInjectiveResolution.map (BoundedOpen.Subsite.restriction f V'.ι n) I).ι) :
    Homotopy bF (FrameHomotopy.Comparison.map f n V F G a ≫ map f n V V' h G I bG) :=
  FrameHomotopy.Comparison.homotopy f n V F G a I bF (map f n V V' h G I bG)
    hF (augmentation f n V V' h G I bG hG)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameTransport.Comparison
