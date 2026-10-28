import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionRegularRepresentative
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenPullbackCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.OpenSquareCoefficient
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenCycle

/-! # Restriction Open Coefficient -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionOpenCoefficient.Cycles

noncomputable section

/-! # LineBundleCycles: canonical rational-section restriction commutes with actual open pullback on prime supports -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle X) (i : Y ⟶ X) [IsOpenImmersion i] (y : Y)

def lineBundlePointSupportOpenIso :
    ((L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i y)))).pullback (Point.SupportMap.BundleCycles.pointSupportMap i y)).sheaf ≅
      ((L.pullback i).pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y))).sheaf :=
  Module.PullbackSquareSections.BundleCycles.modulePullbackSquareIso (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i y))) (Point.SupportMap.BundleCycles.pointSupportMap i y)
    i (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y)) (Point.SupportMap.BundleCycles.pointSupportMap_inclusion i y) L.sheaf

theorem rationalSectionRestrictionCoefficient_open (a : X.functionFieldˣ)
    (hx : coheight (i y) = 1) (hy : coheight y = 1)
    [IsIntegrallyClosed (X.presheaf.stalk (i y))] [IsIntegrallyClosed (Y.presheaf.stalk y)]
    (ha : L.rationalSectionPointDivisorWithCoefficient a (i y) = 0)
    (ha' : (L.pullback i).rationalSectionPointDivisorWithCoefficient (L.openPullbackSectionCoefficient i a) y = 0) :
    (L.pullback i).rationalSectionRestrictionCoefficient (L.openPullbackSectionCoefficient i a) y hy ha' =
      OpenDivisor.Cycles.lineBundleIsoSectionCoefficient (lineBundlePointSupportOpenIso L i y)
        ((L.pullback (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i y)))).openPullbackSectionCoefficient
          (Point.SupportMap.BundleCycles.pointSupportMap i y) (L.rationalSectionRestrictionCoefficient a (i y) hx ha)) := by
  let D := Classical.choice (L.rationalSectionUnitNeighborhood_nonempty a (i y) hx ha)
  let jX := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i y))
  let jY := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm y)
  let q := Point.SupportMap.BundleCycles.pointSupportMap i y
  let U := D.openSet
  let V := i ⁻¹ᵁ U
  let W := jY ⁻¹ᵁ V
  let : Nonempty V := ⟨⟨y, D.point_mem⟩⟩
  let : Nonempty W := Point.SupportOpenEvaluation.BundleCycles.pointSupportPreimage_nonempty Y y V D.point_mem
  let hq : W ≤ (q ≫ jX) ⁻¹ᵁ U := (Point.SupportOpenCycle.BundleCycles.pointSupportMap_open_preimage i y U).ge
  let s := D.localSection
  let t := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen i L.sheaf U s
  let u := Module.OpenPullbackSections.BundleCycles.moduleSectionPullbackOnOpen jX L.sheaf U s
  let M := L.pullback jX
  let b := L.rationalSectionRestrictionCoefficient a (i y) hx ha
  have hs : L.genericSectionCoefficient U s = a.val :=
    (L.genericSectionCoefficient_eq_local (i y) U D.subordinate s).trans D.localSection_coefficient
  have ht : (L.pullback i).genericSectionCoefficient V t = (L.openPullbackSectionCoefficient i a).val :=
    L.genericSectionCoefficient_openPullback_onOpen i a U s hs
  have hu : M.genericSectionCoefficient (jX ⁻¹ᵁ U) u = b.val :=
    congrArg (fun v => v.val) (L.rationalSectionRestrictionCoefficient_eq a (i y) hx ha D).symm
  have hby := (L.pullback i).rationalSectionRestrictionCoefficient_regular
    (L.openPullbackSectionCoefficient i a) y hy ha' V D.point_mem t ht
  have hsq := OpenSquareCoefficient.Cycles.lineBundleOpenSquare_genericCoefficient jX q i jY
    (Point.SupportMap.BundleCycles.pointSupportMap_inclusion i y) L U hq s b hu
  apply Units.ext
  exact hby.trans hsq

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.LineBundle.RestrictionOpenCoefficient.Cycles
