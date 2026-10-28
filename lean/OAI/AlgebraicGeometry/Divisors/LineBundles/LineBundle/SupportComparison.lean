import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.PullbackIso
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.IsoDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.GlobalDivisor
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.Intersection

/-! # Support Comparison -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SupportComparison.Cycles

noncomputable section

/-! # LineBundleCycles: isomorphism invariance and global-triviality vanishing on actual closed supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] {L M : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X}

theorem lineBundleDivisorOnSupport_iso (e : L.sheaf ≅ M.sheaf) (W : IrreducibleCloseds X) :
    Intersection.Cycles.lineBundleDivisorOnSupport L W = Intersection.Cycles.lineBundleDivisorOnSupport M W +
      Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W
        (IsoCoefficient.Cycles.lineBundleIsoRationalCoefficient (PullbackIso.Cycles.lineBundlePullbackIso e (CycleClass.Geometric.GenericPoint.reducedSupportι W))).val := by
  change Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) _ = _
  rw [IsoDivisor.Cycles.lineBundleIso_pointCycle (PullbackIso.Cycles.lineBundlePullbackIso e (CycleClass.Geometric.GenericPoint.reducedSupportι W)), Finsupp.mapDomain_add]
  congr 1
  exact (Finsupp.embDomain_eq_mapDomain
    ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩ _).symm

theorem lineBundleDivisorOnSupport_global (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)
    (W : IrreducibleCloseds X) :
    Intersection.Cycles.lineBundleDivisorOnSupport L W = Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W
      (GlobalCoordinate.Cycles.lineBundleGlobalRationalCoefficient (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e (CycleClass.Geometric.GenericPoint.reducedSupportι W))).val := by
  change Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι W) _ = _
  rw [GlobalDivisor.Cycles.lineBundleGlobal_pointCycle (PullbackIso.Cycles.lineBundlePullbackGlobalTrivialization e (CycleClass.Geometric.GenericPoint.reducedSupportι W))]
  exact (Finsupp.embDomain_eq_mapDomain
    ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩ _).symm

theorem lineBundleDivisorOnSupport_class_iso (e : L.sheaf ≅ M.sheaf)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L W) =
      Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport M W) := by
  rw [lineBundleDivisorOnSupport_iso e, map_add, Point.CycleChow.BundleCycles.pointCycleToChowQ_principal f d W hW, add_zero]

theorem lineBundleDivisorOnSupport_class_global (e : L.sheaf ≅ DivisorClass.Chern.Line.Bundles.Construction.structureModule X)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (W : IrreducibleCloseds X)
    (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1) :
    Point.CycleChow.BundleCycles.pointCycleToChowQ f d (Intersection.Cycles.lineBundleDivisorOnSupport L W) = 0 := by
  rw [lineBundleDivisorOnSupport_global e, Point.CycleChow.BundleCycles.pointCycleToChowQ_principal f d W hW]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SupportComparison.Cycles
