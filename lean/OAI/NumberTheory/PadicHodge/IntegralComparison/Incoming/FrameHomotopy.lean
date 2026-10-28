import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Change
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite
import OAI.NumberTheory.PadicHodge.IntegralComparison.ExactInjectiveResolution
import OAI.NumberTheory.PadicHodge.IntegralComparison.Augmented.ResolutionHomotopy

/-! # Frame Homotopy -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameHomotopy.Comparison

noncomputable section

/-! Changing a genuine resolving frame on a fixed incoming subsite
preserves every augmentation-compatible injective comparison up to
one sheaf-complex homotopy. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) [IsSeparated fY] (n : ℕ)
  (V : Y.Opens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY V.ι n

variable (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)

def complex := ((R).mapHomologicalComplex (.up ℕ)).obj (Bounded.RelativeSheafComplex.complex fY n F)

def augmentation := (ExactInjectiveResolution.sourceIso R).inv ≫
  ((R).mapHomologicalComplex (.up ℕ)).map (Bounded.RelativeSheafComplex.augmentation fY n F)

variable (G : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n) (a : G ⟶ F)

def map : complex fY n V F ⟶ complex fY n V G :=
  ((R).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.Change.sheafMap a)

theorem map_augmentation : augmentation fY n V F ≫ Comparison.map fY n V F G a = augmentation fY n V G :=
  (Category.assoc _ _ _).trans
    (congrArg (fun b => (ExactInjectiveResolution.sourceIso R).inv ≫ b)
      ((((R).mapHomologicalComplex (.up ℕ)).map_comp
        (Bounded.RelativeSheafComplex.augmentation fY n F) (BoundedFrame.Change.sheafMap a)).symm.trans
        (congrArg ((R).mapHomologicalComplex (.up ℕ)).map (BoundedFrame.Change.sheaf_augmentation a))))

variable (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  [QuasiIso (augmentation fY n V F)]
  (bF : complex fY n V F ⟶ (ExactInjectiveResolution.map
    (BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY V.ι n) I).cocomplex)
  (bG : complex fY n V G ⟶ (ExactInjectiveResolution.map
    (BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY V.ι n) I).cocomplex)
  (hF : augmentation fY n V F ≫ bF = (ExactInjectiveResolution.map
    (BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY V.ι n) I).ι)
  (hG : augmentation fY n V G ≫ bG = (ExactInjectiveResolution.map
    (BoundedOpen.Subsite.restriction (p := p) (J := J) (δ := δ) fY V.ι n) I).ι)

def homotopy : Homotopy bF (Comparison.map fY n V F G a ≫ bG) :=
  Augmented.ResolutionHomotopy.homotopy _ (augmentation fY n V F)
    (ExactInjectiveResolution.map R I) bF _
    (hF.trans (((Category.assoc _ _ _).symm.trans
      ((congrArg (fun b => b ≫ bG) (map_augmentation fY n V F G a)).trans hG)).symm))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Incoming.FrameHomotopy.Comparison
