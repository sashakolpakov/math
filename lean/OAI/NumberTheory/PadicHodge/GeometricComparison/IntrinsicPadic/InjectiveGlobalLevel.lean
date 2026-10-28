import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel

/-! # Injective Global Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel

noncomputable section

/-! The named native injective Cech comparison computes original global
bounded crystalline cohomology naturally in the original level transition. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) (f : Y.left ⟶ X.left)
  (n m : ℕ) (hnm : n ≤ m)
  (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y)))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "Iq" => fun q : ℕ => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution wittMap q I
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f

def totalIso (q : ℕ) : (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I q).total (.up ℕ) ≅ (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.target p X Y f I q).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I q) (.up ℕ)

def totalMap : (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I m).total (.up ℕ) ⟶ (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I n).total (.up ℕ) :=
  HomologicalComplex₂.total.map (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.nativeMap p X Y f n m hnm I) (.up ℕ)

theorem total_natural : totalMap p X Y f n m hnm I ≫ (totalIso p X Y f I n).hom =
    (totalIso p X Y f I m).hom ≫ Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel.totalMap wittMap n m hnm I U := by
  let T := HomologicalComplex₂.totalFunctor (ModuleCat.{2} R) (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.nativeMap p X Y f n m hnm I)
    (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I n).hom).symm.trans
      ((congrArg T.map (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.bicomplex_natural p X Y f n m hnm I)).trans
        (T.map_comp (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevel.comparisonIso p X Y f I m).hom (InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.targetMap p X Y f n m hnm I)))

def homologyIso (q i : ℕ) : ((InjectiveCechLevel.IntrinsicPadicInjectiveCechLevelData.native p X Y f I q).total (.up ℕ)).homology i ≅
    ModuleCat.of R (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap q i) :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{2} R) (.up ℕ) i).mapIso (totalIso p X Y f I q) ≪≫
    Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso wittMap q (Iq q) U (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) i

theorem homology (i : ℕ) : HomologicalComplex.homologyMap (totalMap p X Y f n m hnm I) i ≫
    (homologyIso p X Y f I n i).hom =
    (homologyIso p X Y f I m i).hom ≫ ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map wittMap n m hnm i) := by
  have h₁ := (HomologicalComplex.homologyMap_comp (totalMap p X Y f n m hnm I) (totalIso p X Y f I n).hom i).symm.trans
    ((congrArg (fun q => HomologicalComplex.homologyMap q i) (total_natural p X Y f n m hnm I)).trans
      (HomologicalComplex.homologyMap_comp (totalIso p X Y f I m).hom (Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel.totalMap wittMap n m hnm I U) i))
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁
    (Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel.homology wittMap n m hnm I U (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveGlobalLevel.IntrinsicPadicInjectiveGlobalLevel
