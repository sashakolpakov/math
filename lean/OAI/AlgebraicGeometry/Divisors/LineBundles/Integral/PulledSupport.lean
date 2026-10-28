import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberOpen
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberFieldNaturality
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Pulled Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: actual integral inverse images of closed supports under smooth integral-fiber maps -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [Smooth f] [GeometricallyIntegral f]
    [IsLocallyNoetherian Y] (W : IrreducibleCloseds Y)

def integralPulledSupportScheme : Scheme := pullback f (CycleClass.Geometric.GenericPoint.reducedSupportι W)

def integralPulledSupportInclusion : integralPulledSupportScheme f W ⟶ X :=
  pullback.fst f (CycleClass.Geometric.GenericPoint.reducedSupportι W)

def integralPulledSupportProjection : integralPulledSupportScheme f W ⟶ CycleClass.Geometric.GenericPoint.reducedSupportScheme W :=
  pullback.snd f (CycleClass.Geometric.GenericPoint.reducedSupportι W)

instance integralPulledSupportInclusion_isClosedImmersion : IsClosedImmersion (integralPulledSupportInclusion f W) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst f (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

instance integralPulledSupportProjection_smooth : Smooth (integralPulledSupportProjection f W) :=
  inferInstanceAs (Smooth (pullback.snd f (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

instance integralPulledSupportProjection_geometricallyIntegral : GeometricallyIntegral (integralPulledSupportProjection f W) :=
  inferInstanceAs (GeometricallyIntegral (pullback.snd f (CycleClass.Geometric.GenericPoint.reducedSupportι W)))

instance integralPulledSupportScheme_isIntegral : IsIntegral (integralPulledSupportScheme f W) :=
  GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (integralPulledSupportProjection f W)

omit [Smooth f] [GeometricallyIntegral f] [IsLocallyNoetherian Y] in
theorem integralPulledSupport_isPullback :
    IsPullback (integralPulledSupportProjection f W) (integralPulledSupportInclusion f W) (CycleClass.Geometric.GenericPoint.reducedSupportι W) f :=
  (IsPullback.of_hasPullback f (CycleClass.Geometric.GenericPoint.reducedSupportι W)).flip

def integralPulledSupport : IrreducibleCloseds X :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (integralPulledSupportInclusion f W)

theorem integralPulledSupport_coe : (integralPulledSupport f W : Set X) = f ⁻¹' (W : Set Y) := by
  change closure (Set.range (integralPulledSupportInclusion f W)) = _
  rw [(integralPulledSupportInclusion f W).isClosedEmbedding.isClosed_range.closure_eq]
  have h := Scheme.image_preimage_eq_of_isPullback (integralPulledSupport_isPullback f W) Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h.trans (congrArg (fun A : Set Y => f ⁻¹' A) (CycleClass.Geometric.GenericPoint.range_reducedSupportι W))

theorem integralPulledSupport_genericPoint :
    irreducibleSetEquivPoints (integralPulledSupport f W) =
      FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (irreducibleSetEquivPoints W) := by
  exact (ClosedImage.BundleCycles.integralClosedImage_genericPoint (integralPulledSupportInclusion f W)).trans
    ((congrArg (integralPulledSupportInclusion f W)
      (FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic (integralPulledSupportProjection f W)).symm).trans
        ((FiberOpen.BundleCycles.integralFiberGenericPoint_naturality f (integralPulledSupportProjection f W)
          (CycleClass.Geometric.GenericPoint.reducedSupportι W) (integralPulledSupportInclusion f W)
          (integralPulledSupport_isPullback f W) _).trans
            (congrArg (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W))))

theorem integralPulledSupport_eq_pointClosure : integralPulledSupport f W =
    irreducibleSetEquivPoints.symm (FiberGenericPoint.BundleCycles.integralFiberGenericPoint f (irreducibleSetEquivPoints W)) :=
  irreducibleSetEquivPoints.injective ((integralPulledSupport_genericPoint f W).trans
    (irreducibleSetEquivPoints.apply_symm_apply _).symm)

def integralPulledSupportFunction (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (integralPulledSupport f W)).functionField :=
  ClosedImage.BundleCycles.integralClosedImageFunction (integralPulledSupportInclusion f W)
    (FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (integralPulledSupportProjection f W) g)

theorem integralPulledSupportFunction_ne_zero (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    integralPulledSupportFunction f W g ≠ 0 :=
  ClosedImage.BundleCycles.integralClosedImageFunction_ne_zero (integralPulledSupportInclusion f W) _
    (FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_ne_zero (integralPulledSupportProjection f W) g hg)

end

/-! # LineBundleCycles: the actual closed inverse image of a support is Noetherian -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace

instance integralPulledSupportScheme_isNoetherian {E X : Scheme.{0}}
    [AlgebraicGeometry.IsNoetherian E] (p : E ⟶ X) (W : IrreducibleCloseds X) :
    AlgebraicGeometry.IsNoetherian (integralPulledSupportScheme p W) := by
  have : IsLocallyNoetherian (pullback p (CycleClass.Geometric.GenericPoint.reducedSupportι W)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.fst p (CycleClass.Geometric.GenericPoint.reducedSupportι W))
  have : CompactSpace (pullback p (CycleClass.Geometric.GenericPoint.reducedSupportι W) : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst p (CycleClass.Geometric.GenericPoint.reducedSupportι W))
  change AlgebraicGeometry.IsNoetherian (pullback p (CycleClass.Geometric.GenericPoint.reducedSupportι W))
  exact ⟨⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.PulledSupport.BundleCycles
