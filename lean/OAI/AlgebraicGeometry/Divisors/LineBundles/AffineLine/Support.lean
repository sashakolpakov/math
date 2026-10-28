import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.GenericPoint
import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.ClosedImage

/-! # Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual inverse images of closed integral supports in the relative affine line -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) (W : IrreducibleCloseds X)

def affineLineSupportMap : Charts.BundleCycles.affineLine (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ⟶ Charts.BundleCycles.affineLine X :=
  AffineSpace.map PUnit (CycleClass.Geometric.GenericPoint.reducedSupportι W)

theorem affineLineSupport_isPullback :
    IsPullback (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (affineLineSupportMap X W)
      (CycleClass.Geometric.GenericPoint.reducedSupportι W) (Charts.BundleCycles.affineLineProjection X) :=
  (AffineSpace.isPullback_map (n := PUnit) (CycleClass.Geometric.GenericPoint.reducedSupportι W)).flip

instance affineLineSupportMap_isClosedImmersion : IsClosedImmersion (affineLineSupportMap X W) :=
  MorphismProperty.of_isPullback (affineLineSupport_isPullback X W) inferInstance

def affineLineExtendedSupport : IrreducibleCloseds (Charts.BundleCycles.affineLine X) :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (affineLineSupportMap X W)

theorem affineLineExtendedSupport_genericPoint :
    irreducibleSetEquivPoints (affineLineExtendedSupport X W) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (irreducibleSetEquivPoints W) := by
  exact (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (affineLineSupportMap X W)).trans
    ((congrArg (affineLineSupportMap X W)
      (Integral.FiberFieldNaturality.BundleCycles.integralFiberGenericPoint_generic (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))).symm).trans
        ((Integral.FiberOpen.BundleCycles.integralFiberGenericPoint_naturality (Charts.BundleCycles.affineLineProjection X)
          (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) (CycleClass.Geometric.GenericPoint.reducedSupportι W) (affineLineSupportMap X W)
          (affineLineSupport_isPullback X W) _).trans
            (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W))))

theorem affineLineExtendedSupport_coe : (affineLineExtendedSupport X W : Set (Charts.BundleCycles.affineLine X)) =
    Charts.BundleCycles.affineLineProjection X ⁻¹' (W : Set X) := by
  change closure (Set.range (affineLineSupportMap X W)) = _
  rw [(affineLineSupportMap X W).isClosedEmbedding.isClosed_range.closure_eq]
  have h := Scheme.image_preimage_eq_of_isPullback (affineLineSupport_isPullback X W) Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  exact h.trans (congrArg (fun A : Set X => Charts.BundleCycles.affineLineProjection X ⁻¹' A) (CycleClass.Geometric.GenericPoint.range_reducedSupportι W))

theorem affineLineExtendedSupport_eq_pointClosure : affineLineExtendedSupport X W =
    irreducibleSetEquivPoints.symm
      (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (irreducibleSetEquivPoints W)) :=
  irreducibleSetEquivPoints.injective ((affineLineExtendedSupport_genericPoint X W).trans
    (irreducibleSetEquivPoints.apply_symm_apply _).symm)

def affineLineExtendedFunction (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (affineLineExtendedSupport X W)).functionField :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction (affineLineSupportMap X W)
    (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) g)

theorem affineLineExtendedFunction_ne_zero (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (hg : g ≠ 0) :
    affineLineExtendedFunction X W g ≠ 0 :=
  Integral.ClosedImage.BundleCycles.integralClosedImageFunction_ne_zero (affineLineSupportMap X W) _
    (Integral.FiberFieldNaturality.BundleCycles.integralFiberFunctionFieldMap_ne_zero (Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) g hg)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support.BundleCycles
