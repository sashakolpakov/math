import OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeData
import OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.Inverse
import OAI.NumberTheory.PadicHodge.GeometricComparison.CochainInverse

/-! # Typed Reference Global Edge -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceGlobalEdge.IntrinsicPadicTypedReferenceGlobalEdge

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

open OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData

omit [IsSeparated Y.hom] [X.left.IsSeparated] in
theorem flasque_quasiIso : QuasiIso (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) :=
  Bounded.FlasqueCechGlobal.BoundedFlasqueCechGlobalComparison.quasiIso w n I (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.specialCover p X Y f)
    (InjectiveCechGlobal.IntrinsicPadicInjectiveCechGlobal.cover p X Y f)

omit [IsSeparated Y.hom] in
theorem quasiIso : QuasiIso (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X Y f n I) := by
  let : QuasiIso (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) := flasque_quasiIso p X Y f n I
  exact CochainInverse.CochainInverseEdgeHomology.quasiIso (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.comparisonIso p X Y f n I)

omit [IsSeparated Y.hom] in
theorem original_factor (i : ℕ) : TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.originalGlobal p X Y f n I i =
    HomologicalComplex.homologyMap (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.comparisonIso p X Y f n I).hom i ≫ TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.targetGlobal p X Y f n I i :=
  GlobalHomologyFactors.IntrinsicPadicGlobalHomologyFactors.homologyIso_hom p X Y f n I i

omit [IsSeparated Y.hom] [X.left.IsSeparated] in
theorem target_factor (i : ℕ) : HomologicalComplex.homologyMap (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) i ≫
    TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.targetGlobal p X Y f n I i = TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.sectionGlobal p Y n I i := by
  let : QuasiIso (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) := flasque_quasiIso p X Y f n I
  exact (asIso (HomologicalComplex.homologyMap (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) i)).hom_inv_id_assoc
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.sectionGlobal p Y n I i)

omit [IsSeparated Y.hom] in
theorem homology (i : ℕ) : HomologicalComplex.homologyMap (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.edge p X Y f n I) i ≫
    TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.originalGlobal p X Y f n I i = TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.sectionGlobal p Y n I i :=
  Functor.Inverse.FunctorInverseComparison.equality (HomologicalComplex.homologyFunctor (ModuleCat.{2} R) (.up ℕ) i)
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.flasqueEdge p X Y f n I) (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.comparisonIso p X Y f n I)
    (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.sectionGlobal p Y n I i) (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.targetGlobal p X Y f n I i) (TypedReferenceEdgeData.IntrinsicPadicTypedReferenceEdgeData.originalGlobal p X Y f n I i)
    (target_factor p X Y f n I i) (original_factor p X Y f n I i).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.TypedReferenceGlobalEdge.IntrinsicPadicTypedReferenceGlobalEdge
