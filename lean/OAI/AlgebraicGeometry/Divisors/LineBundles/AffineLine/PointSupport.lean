import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.Support

/-! # Point Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport.BundleCycles

noncomputable section

/-! # LineBundleCycles: every affine-line point lifts to the line over the actual closure of its base point -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0})

theorem affineLinePoint_liftSupport (W : IrreducibleCloseds X) (y : Charts.BundleCycles.affineLine X)
    (hy : Charts.BundleCycles.affineLineProjection X y = irreducibleSetEquivPoints W) :
    ∃ q : Charts.BundleCycles.affineLine (CycleClass.Geometric.GenericPoint.reducedSupportScheme W), Support.BundleCycles.affineLineSupportMap X W q = y ∧
      Charts.BundleCycles.affineLineProjection (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) q = genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) := by
  have h : CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) = Charts.BundleCycles.affineLineProjection X y :=
    (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq W).trans hy.symm
  obtain ⟨q, hq, hj⟩ := Scheme.exists_preimage_of_isPullback (Support.BundleCycles.affineLineSupport_isPullback X W)
    (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) y h
  exact ⟨q, hj, hq⟩

theorem affineLineSupportMap_genericPoint (W : IrreducibleCloseds X) :
    Support.BundleCycles.affineLineSupportMap X W (genericPoint (Charts.BundleCycles.affineLine (CycleClass.Geometric.GenericPoint.reducedSupportScheme W))) =
      Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X) (irreducibleSetEquivPoints W) :=
  (Integral.ClosedImage.BundleCycles.integralClosedImage_genericPoint (Support.BundleCycles.affineLineSupportMap X W)).symm.trans
    (Support.BundleCycles.affineLineExtendedSupport_genericPoint X W)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport.BundleCycles
