import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionOpenCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.SectionCycleTransport
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenCycle

/-! # Restriction Open Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionOpenCycle.Cycles

noncomputable section

/-! # LineBundleCycles: the complete canonical restricted-section cycle commutes exactly with actual open pullback -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (i : Y ⟶ X) [IsOpenImmersion i] (y : Y)

theorem restrictedRationalSectionPointCycle_open (a : X.functionFieldˣ)
    (hx : coheight (i y) = 1) (hy : coheight y = 1)
    [IsIntegrallyClosed (X.presheaf.stalk (i y))] [IsIntegrallyClosed (Y.presheaf.stalk y)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a (i y) = 0)
    (ha' : (L.pullback i).rationalSectionPointDivisorWithCoefficient (L.openPullbackSectionCoefficient i a) y = 0) :
    (L.pullback i).restrictedRationalSectionPointCycle (L.openPullbackSectionCoefficient i a) y hy ha' =
      Finsupp.comapDomain i (L.restrictedRationalSectionPointCycle a (i y) hx ha) i.isOpenEmbedding.injective.injOn := by
  let jX := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i y))
  let jY := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y)
  let q := Point.SupportMap.BundleCycles.pointSupportMap i y
  let M := L.pullback jX
  let b := L.rationalSectionRestrictionCoefficient a (i y) hx ha
  have hc := RestrictionOpenCoefficient.Cycles.rationalSectionRestrictionCoefficient_open L i y a hx hy ha ha'
  have hd := SectionCycleTransport.Cycles.lineBundleIso_section_pointCycle (RestrictionOpenCoefficient.Cycles.lineBundlePointSupportOpenIso L i y)
    (M.openPullbackSectionCoefficient q b)
  have ho := M.openPullback_section_pointCycle q b
  have hs := Point.SupportOpenCycle.BundleCycles.pointSupportOpen_pointCycle i y (M.rationalSectionPointCycleWithCoefficient b)
  change Finsupp.mapDomain jY (((L.pullback i).pullback jY).rationalSectionPointCycleWithCoefficient
    ((L.pullback i).rationalSectionRestrictionCoefficient _ y hy ha')) = _
  exact (congrArg (fun c => Finsupp.mapDomain jY
    (((L.pullback i).pullback jY).rationalSectionPointCycleWithCoefficient c)) hc).trans
      ((congrArg (Finsupp.mapDomain jY) hd).trans ((congrArg (Finsupp.mapDomain jY) ho).trans hs.symm))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionOpenCycle.Cycles
