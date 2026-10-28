import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevelGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTotal

/-! # Flasque Cech Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel

noncomputable section

/-! The original flasque Cech/global crystalline comparison commutes with
the actual bounded-level transition on global crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def transformation : IntegralComparison.BoundedOpen.FlasqueComplex.functor (p := p) (J := J) (δ := δ) f m ⟶
    T ⋙ IntegralComparison.BoundedOpen.FlasqueComplex.functor f n where
  app F := ObjectProperty.homMk ((OpenSectionLevel.BoundedOpenSectionLevel.transformation f n m hnm).app F)
  naturality F G α := by
    apply ObjectProperty.hom_ext
    exact (OpenSectionLevel.BoundedOpenSectionLevel.transformation f n m hnm).naturality α

variable (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

local notation "In" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I
local notation "Im" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I

def complexMap : IntegralComparison.BoundedOpen.FlasqueComplex.complex f m Im ⟶ IntegralComparison.BoundedOpen.FlasqueComplex.complex f n In :=
  ((transformation f n m hnm).mapHomologicalComplex (.up ℕ)).app (Im).cocomplex

def totalMap {ι : Type} (U : ι → Y.Opens) :=
  FlasqueCechTotal.FlasqueCechGlobalNaturality.totalMap.{u + 1, u, u + 2} R Y.carrier U (complexMap f n m hnm I)

theorem natural {ι : Type} (U : ι → Y.Opens) : FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map f m Im U ≫
    totalMap f n m hnm I U = OpenSectionLevelGlobal.BoundedOpenSectionLevelGlobal.map f n m hnm I ≫
      FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map f n In U :=
  FlasqueCechTotal.FlasqueCechGlobalNaturality.natural.{u + 1, u, u + 2} R Y.carrier U (complexMap f n m hnm I)

theorem homology {ι : Type} (U : ι → Y.Opens) (hU : iSup U = ⊤) (i : ℕ) :
    HomologicalComplex.homologyMap (totalMap f n m hnm I U) i ≫
      (FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso f n In U hU i).hom =
    (FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso f m Im U hU i).hom ≫
      ModuleCat.ofHom (IntegralComparison.Bounded.CohomologyTransition.map f n m hnm i) := by
  let := FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.quasiIso f m Im U hU
  let := FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.quasiIso f n In U hU
  have h := (HomologicalComplex.homologyMap_comp (FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map f m Im U)
    (totalMap f n m hnm I U) i).symm.trans
      ((congrArg (fun a => HomologicalComplex.homologyMap a i) (natural f n m hnm I U)).trans
        (HomologicalComplex.homologyMap_comp (OpenSectionLevelGlobal.BoundedOpenSectionLevelGlobal.map f n m hnm I)
          (FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map f n In U) i))
  have h₁ := IntegralComparison.InverseCoordinateHomology.inverse
    (asIso (HomologicalComplex.homologyMap (FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map f m Im U) i))
    (asIso (HomologicalComplex.homologyMap (FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map f n In U) i))
    (HomologicalComplex.homologyMap (OpenSectionLevelGlobal.BoundedOpenSectionLevelGlobal.map f n m hnm I) i)
    (HomologicalComplex.homologyMap (totalMap f n m hnm I U) i) h.symm
  exact ExactHomology.ExactHomologyComparison.compose _ _ _ _ _ _ _ h₁ (OpenSectionLevelGlobal.BoundedOpenSectionLevelGlobal.homology f n m hnm I i)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.FlasqueCechLevel.BoundedFlasqueCechLevel
