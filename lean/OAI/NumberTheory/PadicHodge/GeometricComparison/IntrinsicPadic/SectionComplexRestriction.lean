import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor
import OAI.NumberTheory.PadicHodge.GeometricComparison.NonemptyCech.ProductBicomplex

/-! # Section Complex Restriction -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction

noncomputable section

/-! The native section complex is the actual restricted original open-section complex. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left) (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

def comparisonIso :
    ((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
    ((NonemptyCech.ProductBicomplex.NonemptyCechProductBicomplex.pullback (A := ModuleCat.{2} Rcoeff)
      (SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f)).mapHomologicalComplex (.up ℕ)).obj
        (IntegralComparison.BoundedOpen.SectionComplex.complex wittMap n J) := Iso.refl _

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction
