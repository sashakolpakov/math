import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.PuncturedCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.CycleOpenSquare
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationCartier

/-! # Deformation Closure Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationClosureCycle.BundleCycles

noncomputable section

/-! Closing the actual punctured fiber cycles commutes with restriction to an open deformation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y] in
theorem deformationClosureCycleExtension_open (z : Y →₀ ℚ) :
    Finsupp.comapDomain (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) (Global.SpecializationCartier.BundleCycles.deformationClosureCycleExtension I z)
      (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I).isOpenEmbedding.injective.injOn =
      Global.SpecializationCartier.BundleCycles.deformationClosureCycleExtension (I.comap i) (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  exact (Point.CycleOpenSquare.BundleCycles.pointCycle_comap_map_of_isPullback (DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I)
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i)) (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
    (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) (DeformationPunctured.BundleCycles.globalOpenPuncturedMap_isPullback i I)
    (DeformationPunctured.BundleCycles.globalOpenPuncturedMap i I).isOpenEmbedding.injective
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i)).isOpenEmbedding.injective
    (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I).isOpenEmbedding.injective
    (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I).isOpenEmbedding.injective (Punctured.DivisorPullback.BundleCycles.puncturedCycleExtension I z)).trans
    (congrArg (Finsupp.mapDomain (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion (I.comap i)))
      (PuncturedCycle.BundleCycles.puncturedCycleExtension_open i I z))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationClosureCycle.BundleCycles
