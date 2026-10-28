import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceGlobalEdge
import OAI.NumberTheory.PadicHodge.GeometricComparison.FlasqueTransported

/-! # Typed Reference Edge Coordinates -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeCoordinates.IntrinsicPadicTypedReferenceEdgeCoordinates

noncomputable section

/-! The inverse of the original native comparison gives precisely
the canonical global cone edge, checked on each degree. -/

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

omit [IsSeparated Y.hom] in
theorem inverse_component (q r : ℕ) : ((TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.comparison p X Y f n I).inv.f q).f r =
    ((Cech.TransportedCone.CechTransportedCone.bicomplexIso F U
      (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n I)
      (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso w n I)).inv.f q).f r := rfl

def inverseEdgeComponent (q : ℕ) :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.global p Y n I).X q ⟶
      (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.source p X Y f n I).X q :=
  FlasqueCechGlobal.FlasqueCechGlobalComparison.component.{1, 0, 2} R Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) K q ≫
      ((TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.comparison p X Y f n I).inv.f q).f 0 ≫
        (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X Y f n I)).ιTotal
          (.up ℕ) q 0 q rfl

def transportedEdgeComponent (q : ℕ) :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.global p Y n I).X q ⟶
      (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.source p X Y f n I).X q :=
  FlasqueCechGlobal.FlasqueCechGlobalComparison.component.{1, 0, 2} R Y.left.carrier
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) K q ≫
      ((Cech.TransportedCone.CechTransportedCone.bicomplexIso F U
        (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n I)
        (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso w n I)).inv.f q).f 0 ≫
        (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X Y f n I)).ιTotal
          (.up ℕ) q 0 q rfl

omit [IsSeparated Y.hom] in
theorem original_edge_component (q : ℕ) :
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X Y f n I).f q =
      inverseEdgeComponent p X Y f n I q :=
  InverseCech.InverseCechEdgeCoordinates.component
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I)
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.comparison p X Y f n I).inv q
    (FlasqueCechGlobal.FlasqueCechGlobalComparison.component.{1, 0, 2} R Y.left.carrier
      (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) K q) rfl

omit [IsSeparated Y.hom] in
theorem inverse_coordinates (q : ℕ) : inverseEdgeComponent p X Y f n I q =
    transportedEdgeComponent p X Y f n I q :=
  congrArg (fun a => FlasqueCechGlobal.FlasqueCechGlobalComparison.component.{1, 0, 2} R Y.left.carrier
      (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f) K q ≫ a ≫
        (CechPresheaf.ConeTotal.CechPresheafConeTotal.bicomplex U (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.sections p X Y f n I)).ιTotal
          (.up ℕ) q 0 q rfl) (inverse_component p X Y f n I q 0)

omit [IsSeparated Y.hom] in
theorem transported_edge_component (q : ℕ) :
    (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.edge p X Y f n I).f q =
      transportedEdgeComponent p X Y f n I q :=
  FlasqueTransported.FlasqueTransportedEdgeCoordinates.inverse_component.{1, 0, 2} R Y.left.carrier K F U
    (SectionComplexRestriction.IntrinsicPadicSectionComplexRestriction.comparisonIso p X Y f n I)
    (IntegralComparison.BoundedOpen.FlasqueComplex.underlyingComplexIso w n I) q

omit [IsSeparated Y.hom] in
theorem edge_component (q : ℕ) : (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X Y f n I).f q =
    (GlobalConeCoordinates.IntrinsicPadicGlobalConeCoordinates.edge p X Y f n I).f q :=
  (original_edge_component p X Y f n I q).trans
    ((inverse_coordinates p X Y f n I q).trans
      (transported_edge_component p X Y f n I q).symm)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeCoordinates.IntrinsicPadicTypedReferenceEdgeCoordinates
