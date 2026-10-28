import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFiniteMapData
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalComposite
import OAI.NumberTheory.PadicHodge.GeometricComparison.BicomplexComposite

/-! # Integral Finite Composite Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFiniteCompositeCoordinates.IntrinsicPadicIntegralFiniteCompositeCoordinates

noncomputable section

/-! The original finite cochain composite has the checked complete
integral-to-flasque H-one coordinates at the restricted big resolution. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe uR vR
private theorem module_homology {R : Type uR} [CommRing R]
    {K L M : HomologicalComplex₂ (ModuleCat.{vR} R) (.up ℕ) (.up ℕ)}
    (a : K ⟶ L) (b : L ⟶ M) (c : K ⟶ M) (i : ℕ)
    (h : ∀ q r, q + r = i → (a.f q).f r ≫ (b.f q).f r = (c.f q).f r) :
    HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map a (.up ℕ) ≫ HomologicalComplex₂.total.map b (.up ℕ)) i =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map c (.up ℕ)) i :=
  BicomplexComposite.BicomplexCompositeHomology.homology a b c i h

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y))) (n : ℕ)

local notation "Iq" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n I

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "E" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

theorem component (q r : ℕ) :
    (((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq)).f q).f r ≫
      ((InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom.f q).f r =
    ((IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.finiteBicomplex p X Y f hp I n).f q).f r := rfl

private abbrev homologyProof :=
  module_homology
    ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R E).map
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq))
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom
    (IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.finiteBicomplex p X Y f hp I n) 1
    (fun q r _ => component p X Y f hp I n q r)

theorem homology : type_of% (homologyProof p X Y f hp I n) :=
  homologyProof p X Y f hp I n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFiniteCompositeCoordinates.IntrinsicPadicIntegralFiniteCompositeCoordinates
