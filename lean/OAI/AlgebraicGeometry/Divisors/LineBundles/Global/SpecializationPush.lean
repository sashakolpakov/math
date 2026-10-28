import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ImageRegularFunction

/-! # Specialization Push -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationPush.BundleCycles

noncomputable section

/-! # LineBundleCycles: the full global specialization pushes to the actual support parameter divisor -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (I P : X.IdealSheafData) [IsIntegral P.subscheme]

theorem globalClosedSupportSpecialization_push :
    Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I) (Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P) =
      Finsupp.mapDomain (SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Support.Specialization.BundleCycles.globalSupportParameterDivisor I P) := by
  have hc : SpecialFiber.BundleCycles.globalSpecialFiberMap I ∘ Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P =
      SupportDeformation.BundleCycles.globalSupportDeformationMap I P ∘ Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P :=
    funext fun x => (congrArg (fun k => k x)
      (pullback.condition (f := SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (g := SpecialFiber.BundleCycles.globalSpecialFiberMap I))).symm
  have hz : Finsupp.mapDomain (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P) (Support.Specialization.BundleCycles.globalSupportFiberCycle I P) =
      Support.Specialization.BundleCycles.globalSupportParameterDivisor I P :=
    (Finsupp.embDomain_eq_mapDomain (Support.Specialization.BundleCycles.globalSupportFiberPointEmbedding I P) (Support.Specialization.BundleCycles.globalSupportFiberCycle I P)).symm.trans
      (Support.Specialization.BundleCycles.globalSupportFiberCycle_push I P)
  change Finsupp.mapDomain (SpecialFiber.BundleCycles.globalSpecialFiberMap I)
    (Finsupp.embDomain (Support.Specialization.BundleCycles.globalSupportConePointEmbedding I P) (Support.Specialization.BundleCycles.globalSupportFiberCycle I P)) = _
  rw [Finsupp.embDomain_eq_mapDomain, ← Finsupp.mapDomain_comp]
  exact (congrArg (fun h => Finsupp.mapDomain h (Support.Specialization.BundleCycles.globalSupportFiberCycle I P)) hc).trans
    (Finsupp.mapDomain_comp.trans (congrArg (Finsupp.mapDomain (SupportDeformation.BundleCycles.globalSupportDeformationMap I P)) hz))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SpecializationPush.BundleCycles
