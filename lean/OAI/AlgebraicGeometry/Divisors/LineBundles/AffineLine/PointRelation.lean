import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointSupport
import OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.HorizontalCycle

/-! # Point Relation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation.BundleCycles

noncomputable section

/-! # LineBundleCycles: every nonextended affine-line point has an actual principal-divisor relation with an extended base cycle -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X]

theorem affineLineNonextendedPoint_cycle_relation (y : Charts.BundleCycles.affineLine X)
    (hy : y ∉ Set.range (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X))) :
    ∃ W : IrreducibleCloseds (Charts.BundleCycles.affineLine X), ∃ g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField,
      g ≠ 0 ∧ ∃ z : X →₀ ℚ,
      Finsupp.single y 1 + Integral.FiberGenericPoint.BundleCycles.integralFiberCycleExtension (Charts.BundleCycles.affineLineProjection X) z = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W g := by
  let V := irreducibleSetEquivPoints.symm (Charts.BundleCycles.affineLineProjection X y)
  have hV : irreducibleSetEquivPoints V = Charts.BundleCycles.affineLineProjection X y := irreducibleSetEquivPoints.apply_symm_apply _
  obtain ⟨q, hjq, hqbase⟩ := PointSupport.BundleCycles.affineLinePoint_liftSupport X V y hV.symm
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme V
  let j := Support.BundleCycles.affineLineSupportMap X V
  have hq : q ≠ genericPoint (Charts.BundleCycles.affineLine A) := by
    intro h
    apply hy
    refine ⟨Charts.BundleCycles.affineLineProjection X y, ?_⟩
    exact (congrArg (Integral.FiberGenericPoint.BundleCycles.integralFiberGenericPoint (Charts.BundleCycles.affineLineProjection X)) hV).symm.trans
      ((PointSupport.BundleCycles.affineLineSupportMap_genericPoint X V).symm.trans ((congrArg j h).symm.trans hjq))
  obtain ⟨a, ha, z, hz⟩ := HorizontalCycle.BundleCycles.affineLineHorizontalPoint_cycle_relation A q hqbase hq
  let W := Support.BundleCycles.affineLineExtendedSupport X V
  let g := Integral.ClosedImage.BundleCycles.integralClosedImageFunction j a
  have hg : g ≠ 0 := Integral.ClosedImage.BundleCycles.integralClosedImageFunction_ne_zero j a ha
  refine ⟨W, g, hg, Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι V) z, ?_⟩
  have h := congrArg (Finsupp.mapDomain j) hz
  rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, hjq,
    Integral.ClosedImage.BundleCycles.integralClosedImage_principalDivisor] at h
  have hn := Integral.FiberOpen.BundleCycles.integralFiberCycleExtension_naturality (Charts.BundleCycles.affineLineProjection X) (Charts.BundleCycles.affineLineProjection A)
    (CycleClass.Geometric.GenericPoint.reducedSupportι V) j (Support.BundleCycles.affineLineSupport_isPullback X V) z
  exact (congrArg (fun b => Finsupp.single y 1 + b) hn).symm.trans h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.AffineLine.PointRelation.BundleCycles
