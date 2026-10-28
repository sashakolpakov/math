import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage
import OAI.AlgebraicGeometry.Divisors.LineBundles.RationalDivisorRestriction

/-! # Support Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: restriction of an actual integral closed support to an open

The scheme-theoretic pullback is an open subscheme of the original
integral support and a closed subscheme of the ambient open. When
nonempty it is integral and isomorphic to the reduced support of the
actual inverse-image closed subset.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Scheme} (i : X ⟶ Y) [IsOpenImmersion i] (W : IrreducibleCloseds Y)

def openSupportPullback : Scheme := pullback i (CycleClass.Geometric.GenericPoint.reducedSupportι W)

def openSupportInclusion : openSupportPullback i W ⟶ X := pullback.fst _ _

def openSupportToOriginal : openSupportPullback i W ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W := pullback.snd _ _

instance openSupportInclusion_isClosedImmersion : IsClosedImmersion (openSupportInclusion i W) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst i (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

instance openSupportToOriginal_isOpenImmersion : IsOpenImmersion (openSupportToOriginal i W) :=
  inferInstanceAs (IsOpenImmersion (pullback.snd i (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

omit [IsOpenImmersion i] in
theorem openSupportInclusion_range : Set.range (openSupportInclusion i W) = i ⁻¹' (W : Set Y) := by
  have h := Scheme.image_preimage_eq_of_isPullback (IsPullback.of_hasPullback i (CycleClass.Geometric.GenericPoint.reducedSupportι W)).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ, CycleClass.Geometric.GenericPoint.range_reducedSupportι] at h
  exact h

omit [IsOpenImmersion i] in
theorem openSupportPullback_nonempty_iff : Nonempty (openSupportPullback i W) ↔ (i ⁻¹' (W : Set Y)).Nonempty := by
  rw [← openSupportInclusion_range]
  exact Set.range_nonempty_iff_nonempty.symm

variable [Nonempty (openSupportPullback i W)]

instance openSupportPullback_isIntegral : IsIntegral (openSupportPullback i W) :=
  isIntegral_of_isOpenImmersion (openSupportToOriginal i W)

def openRestrictedSupport : IrreducibleCloseds X := CycleClass.Geometric.StratumClosure.integralImageClosure (openSupportInclusion i W)

theorem openRestrictedSupport_coe : (openRestrictedSupport i W : Set X) = i ⁻¹' (W : Set Y) :=
  (openSupportInclusion i W).isClosedEmbedding.isClosed_range.closure_eq.trans (openSupportInclusion_range i W)

def openSupportIso : openSupportPullback i W ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (openRestrictedSupport i W) := by
  have he : IsIso (CycleClass.Geometric.StratumClosure.toReducedImageClosure (openSupportInclusion i W)) := by
    change IsIso ((openSupportInclusion i W).toImage ≫ (CycleClass.Geometric.StratumClosure.reducedImageClosureIso (openSupportInclusion i W)).hom)
    infer_instance
  exact @asIso _ _ _ _ (CycleClass.Geometric.StratumClosure.toReducedImageClosure (openSupportInclusion i W)) he

theorem openSupportIso_inclusion :
    (openSupportIso i W).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) = openSupportInclusion i W :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion (openSupportInclusion i W)

def openRestrictedSupportMap : CycleClass.Geometric.GenericPoint.reducedSupportScheme (openRestrictedSupport i W) ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W :=
  (openSupportIso i W).inv ≫ openSupportToOriginal i W

instance openRestrictedSupportMap_isOpenImmersion : IsOpenImmersion (openRestrictedSupportMap i W) := by
  change IsOpenImmersion ((openSupportIso i W).inv ≫ openSupportToOriginal i W)
  infer_instance

theorem openRestrictedSupportMap_inclusion :
    openRestrictedSupportMap i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W = CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) ≫ i := by
  have hp : openSupportInclusion i W ≫ i = openSupportToOriginal i W ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W := pullback.condition
  have he : (openSupportIso i W).inv ≫ openSupportInclusion i W = CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) :=
    (congrArg (fun g => (openSupportIso i W).inv ≫ g) (openSupportIso_inclusion i W).symm).trans
      (Iso.inv_hom_id_assoc _ _)
  change ((openSupportIso i W).inv ≫ openSupportToOriginal i W) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι W = _
  exact (Category.assoc _ _ _).trans ((congrArg (fun g => (openSupportIso i W).inv ≫ g) hp.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (fun g => g ≫ i) he)))

theorem openRestrictedSupport_dimension (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (openRestrictedSupport i W) (i ≫ f) = Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion (openRestrictedSupportMap i W) (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f)
  have he : openRestrictedSupportMap i W ≫ CycleClass.Geometric.SupportFiniteType.supportStructureMap W f =
      CycleClass.Geometric.SupportFiniteType.supportStructureMap (openRestrictedSupport i W) (i ≫ f) := by
    change openRestrictedSupportMap i W ≫ (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ f) =
      CycleClass.Geometric.GenericPoint.reducedSupportι (openRestrictedSupport i W) ≫ (i ≫ f)
    rw [← Category.assoc, openRestrictedSupportMap_inclusion, Category.assoc]
  exact (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) he.symm).trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction.BundleCycles
