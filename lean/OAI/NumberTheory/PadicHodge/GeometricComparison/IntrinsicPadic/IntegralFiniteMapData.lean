import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralGlobalOne
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalHomologyFactors
import OAI.NumberTheory.PadicHodge.GeometricComparison.MappedFactor

/-! # Integral Finite Map Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData

noncomputable section

/-! Explicit cochain and homology types for the original two factors
of the finite integral crystalline comparison. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left)
  (hp : IsPullback f Y.hom X.hom (Spec.map (CommRingCat.ofHom (PadicInt.toZMod : ℤ_[p] →+* ZMod p))))
  (n : ℕ)

local notation "Rcoeff" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))

local instance coefficientRing : Ring Rcoeff :=
  (inferInstance : CommRing Rcoeff).toRing

local notation "coverNerve" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve (OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X)
local notation "wittMap" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

variable (J : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
  (J := Ideal.span {(p : WittVector p (ZMod p))})
  (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
  (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} Rcoeff) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} Rcoeff) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} Rcoeff

def source : CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff coverNerve).obj
    (AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.complex (.up ℕ) (IntegralInjective.IntrinsicPadicIntegralInjectiveComparison.source p X n))).total (.up ℕ)

def middle : CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  ((Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} Rcoeff coverNerve).obj
    (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)).total (.up ℕ)

def target : CochainComplex (ModuleCat.{2} Rcoeff) ℕ :=
  (FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex.{1, 0, 2} Rcoeff Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)
    (IntegralComparison.BoundedOpen.FlasqueComplex.complex wittMap n J)).total (.up ℕ)

def global : ModuleCat.{2} Rcoeff := ModuleCat.of Rcoeff
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) wittMap n 1)

def first : source p X n ⟶ middle p X Y f n J := IntegralCechOne.IntrinsicPadicIntegralCechHOne.map p X Y f hp n J

def second :=
  HomologicalComplex₂.total.map (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n J).hom (.up ℕ)

def original : (source p X n).homology 1 ⟶ global p Y n :=
  (IntegralGlobalOne.IntrinsicPadicIntegralGlobalHOne.homologyIso p X Y f hp n J).hom

def middleGlobal : (middle p X Y f n J).homology 1 ⟶ global p Y n :=
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.homologyIso p X Y f n J 1).hom

def finalMap : (target p X Y f n J).homology 1 ⟶ global p Y n :=
  (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso wittMap n J
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) 1).hom

def composite : source p X n ⟶ target p X Y f n J := first p X Y f hp n J ≫ second p X Y f n J

theorem original_factor : original p X Y f hp n J =
    HomologicalComplex.homologyMap (first p X Y f hp n J) 1 ≫ middleGlobal p X Y f n J := rfl

omit [IsSeparated Y.hom] in
theorem middle_factor : middleGlobal p X Y f n J =
    HomologicalComplex.homologyMap (second p X Y f n J) 1 ≫ finalMap p X Y f n J :=
  GlobalHomologyFactors.IntrinsicPadicGlobalHomologyFactors.homologyIso_hom p X Y f n J 1

theorem homology_factor : original p X Y f hp n J =
    HomologicalComplex.homologyMap (composite p X Y f hp n J) 1 ≫ finalMap p X Y f n J :=
  MappedFactor.MappedComparisonFactor.equality (𝟭 (CochainComplex (ModuleCat.{2} Rcoeff) ℕ))
    (HomologicalComplex.homologyFunctor (ModuleCat.{2} Rcoeff) (.up ℕ) 1)
    (first p X Y f hp n J) (second p X Y f n J) (finalMap p X Y f n J)
    (HomologicalComplex.homologyMap (first p X Y f hp n J) 1)
    (middleGlobal p X Y f n J) (original p X Y f hp n J) rfl
    (middle_factor p X Y f n J) (original_factor p X Y f hp n J)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.IntegralFiniteMapData.IntrinsicPadicIntegralFiniteMapData
