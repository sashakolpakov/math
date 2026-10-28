import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralLevelCompositeFactor
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFiniteCompositeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.FactorEquality

/-! # Integral Level Global Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralLevelGlobalCoordinates.IntrinsicPadicIntegralLevelGlobalCoordinates

noncomputable section

/-! Identify the original level and finite integral comparisons through
their checked complete integral-to-flasque factors. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe uC vC
private theorem factor_from_components {R : Type uC} [CommRing R]
    {K L M : HomologicalComplex₂ (ModuleCat.{vC} R) (.up ℕ) (.up ℕ)}
    (N : ModuleCat.{vC} R) (b : L ⟶ M) (a : K ⟶ L) (c : K ⟶ M) (i : ℕ)
    (firstMap : K.total (.up ℕ) ⟶ L.total (.up ℕ))
    (secondMap : L.total (.up ℕ) ⟶ M.total (.up ℕ))
    (hfirst : firstMap = HomologicalComplex₂.total.map a (.up ℕ))
    (hsecond : secondMap = HomologicalComplex₂.total.map b (.up ℕ))
    (original : (K.total (.up ℕ)).homology i ⟶ N)
    (middle : (L.total (.up ℕ)).homology i ⟶ N)
    (last last' : (M.total (.up ℕ)).homology i ⟶ N)
    (hf : original = HomologicalComplex.homologyMap firstMap i ≫ middle)
    (hm : middle = HomologicalComplex.homologyMap secondMap i ≫ last)
    (hc : ∀ q r, q + r = i → (a.f q).f r ≫ (b.f q).f r = (c.f q).f r)
    (hl : last = last') :
    original = HomologicalComplex.homologyMap (HomologicalComplex₂.total.map c (.up ℕ)) i ≫ last' := by
  subst firstMap
  subst secondMap
  have hcomp := BicomplexComposite.BicomplexCompositeHomology.homology a b c i hc
  rw [hf, hm, ← Category.assoc, ← HomologicalComplex.homologyMap_comp, hcomp, hl]

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

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

local instance coefficientRing : Ring Rcoeff :=
  (inferInstance : CommRing Rcoeff).toRing

local notation "nerve" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)

omit [X.left.IsSeparated] [IsSeparated Y.hom] in
private theorem finalMap_coordinates : IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.finalMap p X Y f n Iq =
    IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor.finalMap p X Y f I n := rfl

private theorem firstMap_coordinates :
    Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} Rcoeff nerve
      (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq) =
    HomologicalComplex₂.total.map
      ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff nerve).map
        (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq)) (.up ℕ) := rfl

omit [IsSeparated Y.hom] in
private theorem secondMap_coordinates : IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.second p X Y f n Iq =
    HomologicalComplex₂.total.map (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom
      (.up ℕ) := rfl

private abbrev bicomplexFactors := factor_from_components
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.global p Y n)
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n Iq).hom
  ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff nerve).map
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq))
  (IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.finiteBicomplex p X Y f hp I n) 1

private abbrev cochainMaps := bicomplexFactors p X Y f hp I n
  (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.map.{1, 2} Rcoeff nerve
    (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.map p X Y f hp n Iq))
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.second p X Y f n Iq)

private abbrev cochainFactors := cochainMaps p X Y f hp I n
  (firstMap_coordinates p X Y f hp I n)
  (secondMap_coordinates p X Y f I n)

private abbrev originalFactors := cochainFactors p X Y f hp I n
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.original p X Y f hp n Iq)
private abbrev middleFactors := originalFactors p X Y f hp I n
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.middleGlobal p X Y f n Iq)
private abbrev finalFactors := middleFactors p X Y f hp I n
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.finalMap p X Y f n Iq)
private abbrev preparedFactors := finalFactors p X Y f hp I n
  (IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor.finalMap p X Y f I n)

private abbrev finiteFactorProof := preparedFactors p X Y f hp I n
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.original_factor p X Y f hp n Iq)
  (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.middle_factor p X Y f n Iq)
  (fun q r _ => IntegralFiniteCompositeCoordinates.IntrinsicPadicIntegralFiniteCompositeCoordinates.component p X Y f hp I n q r)
  (finalMap_coordinates p X Y f I n)

theorem finite_factor : type_of% (finiteFactorProof p X Y f hp I n) :=
  finiteFactorProof p X Y f hp I n

theorem level_original : (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n).hom =
    IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.original p X Y f hp n Iq :=
  FactorEquality.ComparisonFactorEquality.equality
    (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n).hom
    (IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData.original p X Y f hp n Iq)
    (HomologicalComplex.homologyMap (IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.levelMap p X Y f hp I n) 1)
    (HomologicalComplex.homologyMap (IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.finiteMap p X Y f hp I n) 1)
    (IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor.finalMap p X Y f I n)
    (IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor.finalMap p X Y f I n)
    (IntegralLevelCompositeFactor.IntrinsicPadicIntegralLevelCompositeFactor.level p X Y f hp I n)
    (finite_factor p X Y f hp I n)
    (IntegralGlobalComposite.IntrinsicPadicIntegralGlobalComposite.homology p X Y f hp I n) rfl

theorem homology : (IntegralGlobalLevel.IntrinsicPadicIntegralGlobalLevel.homologyIso p X Y f hp I n).hom =
    (IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X Y f hp n Iq).hom :=
  level_original p X Y f hp I n

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralLevelGlobalCoordinates.IntrinsicPadicIntegralLevelGlobalCoordinates
