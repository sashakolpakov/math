import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationClosureCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.DeformationSpecialFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierOpenPoint

/-! # Global Cycle Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GlobalCycleSpecialization.BundleCycles

noncomputable section

/-! The entire constructed global specialization cycle commutes with actual open restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (i : X ⟶ Y) [IsOpenImmersion i] (I : Y.IdealSheafData)

theorem globalCycleSpecialization_open (z : Y →₀ ℚ) :
    Finsupp.comapDomain (DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap i I) (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization I z)
      (DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap i I).isOpenEmbedding.injective.injOn =
      Global.CycleSpecialization.BundleCycles.globalCycleSpecialization (I.comap i) (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn) := by
  apply Finsupp.mapDomain_injective (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i)).isClosedEmbedding.injective
  have hs := Point.CycleOpenSquare.BundleCycles.pointCycle_comap_map_of_isPullback (DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap i I)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i)) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I)
    (DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap_isPullback i I)
    (DeformationSpecialFiber.BundleCycles.globalOpenSpecialFiberMap i I).isOpenEmbedding.injective
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap (I.comap i)).isClosedEmbedding.injective
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I).isClosedEmbedding.injective
    (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I).isOpenEmbedding.injective (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization I z)
  have hc := Principal.CartierOpenPoint.BundleCycles.principalCartierPointMap_open (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection I) (Global.SpecializationCartier.BundleCycles.deformationClosureCycleExtension I z)
  have hp := congrArg (fun a => Principal.CartierFiber.BundleCycles.principalCartierPointMap a
    (Finsupp.comapDomain (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) (Global.SpecializationCartier.BundleCycles.deformationClosureCycleExtension I z)
      (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I).isOpenEmbedding.injective.injOn))
    (DeformationTo.BundleCycles.globalOpenDeformationMap_parameterSection i I)
  exact hs.symm.trans
    ((congrArg (fun c => Finsupp.comapDomain (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I) c
      (Global.OpenDeformationMap.BundleCycles.globalOpenDeformationMap i I).isOpenEmbedding.injective.injOn)
      (Global.SpecializationCartier.BundleCycles.globalCycleSpecialization_push_cartier I z)).trans
      (hc.trans (hp.trans
        ((congrArg (Principal.CartierFiber.BundleCycles.principalCartierPointMap (Global.Specialization.BundleCycles.globalDeformationParameterSection (I.comap i)))
          (DeformationClosureCycle.BundleCycles.deformationClosureCycleExtension_open i I z)).trans
          (Global.SpecializationCartier.BundleCycles.globalCycleSpecialization_push_cartier (I.comap i)
            (Finsupp.comapDomain i z i.isOpenEmbedding.injective.injOn)).symm))))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.GlobalCycleSpecialization.BundleCycles
