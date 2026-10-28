import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalHomologyFactors

/-! # Typed Reference Edge Data -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData

noncomputable section

/-! Define the global edge through the inverse of the original
native comparison, retaining its original homology coordinates literally. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]
  (X : Over (Spec (CommRingCat.of ℤ_[p]))) [IsProper X.hom] [Smooth X.hom] [X.left.IsSeparated]
  (Y : Over (Spec (CommRingCat.of (ZMod p)))) [IsSeparated Y.hom]
  (f : Y.left ⟶ X.left) (n : ℕ)
  (I : InjectiveResolution (IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))}) (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p))
    (IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y) n))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y
local notation "U" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.CechSliceResolution.IntrinsicPadicCechSliceResolution.opens p X
local notation "F" => OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens p X Y f
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex w n I

local instance limits : HasLimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasLimitsOfSize.{0, 0, 2, 1}
local instance colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{2} R) := ModuleCat.hasColimitsOfSize.{2, 1, 0, 0} R

local instance tuple_preserves (m : ℕ) (t : Fin (m + 1) → Integral.EtaleAffineCover.IntegralEtaleAffineCover.Index ℤ_[p] X) :
    PreservesLimit (Discrete.functor (U ∘ t)) F := by
  dsimp only [SectionBifunctor.IntrinsicPadicSectionBifunctor.specialOpens]
  infer_instance

def sourceBicomplex : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  (Cech.TotalOneQuasiIso.CechTotalHOneQuasiIso.bicomplex.{1, 2} R (IntegralComparison.NonemptyCechNerve.nerve U)).obj
    (((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)

def targetBicomplex : HomologicalComplex₂ (ModuleCat.{2} R) (.up ℕ) (.up ℕ) :=
  FlasqueCechGlobal.FlasqueCechGlobalComparison.bicomplex.{1, 0, 2} R Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) K

def comparison : sourceBicomplex p X Y f n I ≅ targetBicomplex p X Y f n I :=
  InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.bicomplexIso p X Y f n I

def source : CochainComplex (ModuleCat.{2} R) ℕ := (sourceBicomplex p X Y f n I).total (.up ℕ)
def target : CochainComplex (ModuleCat.{2} R) ℕ := (targetBicomplex p X Y f n I).total (.up ℕ)
def global : CochainComplex (ModuleCat.{2} R) ℕ := GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.global p Y n I

def comparisonIso : source p X Y f n I ≅ target p X Y f n I :=
  HomologicalComplex₂.total.mapIso (comparison p X Y f n I) (.up ℕ)

def flasqueEdge : global p Y n I ⟶ target p X Y f n I :=
  Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.map w n I (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)

def edge : global p Y n I ⟶ source p X Y f n I :=
  flasqueEdge p X Y f n I ≫ (comparisonIso p X Y f n I).inv

def cohomology (i : ℕ) : ModuleCat.{2} R := ModuleCat.of R
  (IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
    (J := Ideal.span {(p : WittVector p (ZMod p))})
    (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n i)

def originalGlobal (i : ℕ) : (source p X Y f n I).homology i ⟶ cohomology p Y n i :=
  (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.homologyIso p X Y f n I i).hom

def targetGlobal (i : ℕ) : (target p X Y f n I).homology i ⟶ cohomology p Y n i :=
  (Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.homologyIso w n I
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f) i).hom

def sectionGlobal (i : ℕ) : (global p Y n I).homology i ⟶ cohomology p Y n i :=
  (IntegralComparison.BoundedOpen.SectionGlobal.homologyIso w n I i).hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData
