import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportRestriction

/-! # Open Support Pullback -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSupportPullback.Cycles

noncomputable section

/-! # LineBundleCycles: actual line-bundle pullbacks on the open restriction of an integral support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

def lineBundleOpenSupportPullbackIso {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle Y) (W : IrreducibleCloseds Y) [Nonempty (Open.SupportRestriction.BundleCycles.openSupportPullback i W)] :
    (((L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι W)).pullback (Open.SupportRestriction.BundleCycles.openRestrictedSupportMap i W)).sheaf) ≅
      (((L.pullback i).pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W))).sheaf) :=
  PullbackIso.Cycles.lineBundlePullbackCompIso L (Open.SupportRestriction.BundleCycles.openRestrictedSupportMap i W) (CycleClass.Geometric.GenericPoint.reducedSupportι W) ≪≫
    (Scheme.Modules.pullbackCongr (Open.SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion i W)).app L.sheaf ≪≫
    (PullbackIso.Cycles.lineBundlePullbackCompIso L (CycleClass.Geometric.GenericPoint.reducedSupportι (Open.SupportRestriction.BundleCycles.openRestrictedSupport i W)) i).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSupportPullback.Cycles
