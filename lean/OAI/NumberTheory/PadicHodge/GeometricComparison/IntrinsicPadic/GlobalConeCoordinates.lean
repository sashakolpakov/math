import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.InjectiveCechGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Bounded.CechConeGlobal
import OAI.NumberTheory.PadicHodge.GeometricComparison.Cech.TransportedCone
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechTopConeCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueCechTransportedGlobal

/-! # Global Cone Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates

noncomputable section

/-! The original native injective Cech comparison is characterized
by the same canonical global edge as the indexed flasque comparison. -/

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

def sections := ((SectionBifunctor.IntrinsicPadicSectionBifunctor.sections p X Y f n).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

def global := FlasqueCechGlobal.FlasqueCechGlobalComparison.globalComplex.{1, 0, 2} R Y.left.carrier K

def cone := FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.cone.{1, 0, 2} R Y.left.carrier K F
  (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n I)
  (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso w n I)

def bicomplex := CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (sections p X Y f n I)

def edge := FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.edge.{1, 0, 2} R Y.left.carrier K F U
  (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n I)
  (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso w n I)

omit [IsSeparated Y.hom] in
theorem quasiIso : QuasiIso (edge p X Y f n I) :=
  FlasqueCechTransportedGlobal.FlasqueCechTransportedGlobalComparison.quasiIso.{1, 0, 2} R Y.left.carrier K F U
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n I)
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso w n I)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f)
    (IntegralComparison.BoundedOpen.FlasqueComplex.term_flasque w n I)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates
