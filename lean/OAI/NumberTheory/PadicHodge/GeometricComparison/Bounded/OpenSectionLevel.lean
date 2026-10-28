import OAI.NumberTheory.PadicHodge.GeometricComparison.IncomingSection
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.SectionComplex
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.Resolution

/-! # Open Section Level -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevel.BoundedOpenSectionLevel

noncomputable section

/-! Original bounded crystalline open-section functors restrict naturally
between levels, on the actual sheaf and cochain objects. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Opposite

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction
universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def smallTransformation : IntegralComparison.BoundedOpen.SectionPresheaf.functor (p := p) (J := J) (δ := δ) f m ⟶
    T ⋙ IntegralComparison.BoundedOpen.SectionPresheaf.functor f n :=
  Functor.whiskerLeft (sheafToPresheaf (IntegralComparison.BoundedCrystalline.Site.topology f m) (ModuleCat.{u + 1} R))
    (IncomingSection.IncomingSectionFunctorRestriction.transformation R (ModuleCat.of R R) G
      (IntegralComparison.BoundedOpen.SectionPresheaf.property f m) (IntegralComparison.BoundedOpen.SectionPresheaf.property f n)
      (fun _ _ h => h) (IntegralComparison.BoundedOpen.SectionPresheaf.monotone f m)
      (IntegralComparison.BoundedOpen.SectionPresheaf.monotone f n))

def transformation : IntegralComparison.BoundedOpen.SectionComplex.functor (p := p) (J := J) (δ := δ) f m ⟶
    T ⋙ IntegralComparison.BoundedOpen.SectionComplex.functor f n :=
  Functor.whiskerRight (smallTransformation f n m hnm)
    ((Functor.whiskeringRight Y.Opensᵒᵖ (ModuleCat.{u + 1} R) (ModuleCat.{u + 2} R)).obj
      (ModuleCat.uliftFunctor.{u + 2, u + 1} R))

variable (I : InjectiveResolution (IntegralComparison.BigCrystallineCohomology.structureSheaf (p := p) (J := J) (δ := δ) f))

def complexMap :
    IntegralComparison.BoundedOpen.SectionComplex.complex f m (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I) ⟶
      IntegralComparison.BoundedOpen.SectionComplex.complex f n (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f n I) :=
  ((transformation f n m hnm).mapHomologicalComplex (.up ℕ)).app
    (IntegralComparison.BoundedCrystalline.CrystallineCohomology.resolution f m I).cocomplex

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.OpenSectionLevel.BoundedOpenSectionLevel
