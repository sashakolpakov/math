import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Presheaf
import OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.PresheafSectionHomotopy

/-! # Resolution Map Coherence -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionMapCoherence

noncomputable section

/-! The original frame section comparison is natural on homology under augmentation-preserving resolution maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  [QuasiIso (Bounded.RelativeSheafComplex.augmentation f n F)]
  (I I' : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) f n))
  (e : I.cocomplex ⟶ I'.cocomplex) (he : I.ι ≫ e = I'.ι)

include he in
theorem augmentation : Bounded.RelativeSheafComplex.augmentation f n F ≫
    (Injective.Comparison.map f n F I ≫ e) = I'.ι :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ e) (Injective.Comparison.augmentation f n F I)).trans he)

def homotopy : Homotopy (Injective.Comparison.map f n F I ≫ e)
    (Injective.Comparison.map f n F I') :=
  (Injective.Comparison.homotopy f n F I'
    (Injective.Comparison.map f n F I ≫ e) (augmentation f n F I I' e he)).symm

include he in
theorem homology (i : ℕ) :
    HomologicalComplex.homologyMap (Presheaf.Comparison.map f n F I ≫
      ((Sheaf.PresheafSectionComplex.sectionFunctor.{u + 1, u, u + 1, u + 2}
        (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)).mapHomologicalComplex (.up ℕ)).map e) i =
      HomologicalComplex.homologyMap (Presheaf.Comparison.map f n F I') i :=
  Constant.PresheafSectionHomotopy.composition.{u + 1, u, u + 2} (Crystalline.ExactRestriction.Coeff (B := B)) (BoundedCrystalline.Site.topology f n)
    (DeRhamSections.frameComplex f n F) (DeRhamSections.sheafMap f n F)
    (Injective.Comparison.map f n F I) e (Injective.Comparison.map f n F I')
    (homotopy f n F I I' e he) i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.ResolutionMapCoherence
