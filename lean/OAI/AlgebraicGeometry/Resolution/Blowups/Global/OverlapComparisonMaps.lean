import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OverlapChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ComparisonChartPoint

/-! # Overlap Comparison Maps -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapComparisonMaps.Construction

noncomputable section

/-! The two restrictions of a global blowup comparison on a common denominator open. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

theorem globalBlowupOverlapChart_map_left (q : Y ⟶ X)
    (I : X.IdealSheafData) (K : Y.IdealSheafData) (hq : I.comap q = K)
    (hI : I ≠ ⊥) (hK : K ≠ ⊥) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ q ⁻¹ᵁ U.1) (a : I.ideal U) (b c : K.ideal V)
    (hb : b.val = (q.appLE U.1 V.1 hVU).hom a.val)
    (hcenter : (I.ideal U).map (q.appLE U.1 V.1 hVU).hom = K.ideal V) :
    GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart K hK V b c ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK =
      Spec.map (CommRingCat.ofHom ((Blowup.ChartOverlap.Construction.blowupChartOverlapLeft (K.ideal V) b c).comp
        (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo (I.ideal U) a (q.appLE U.1 V.1 hVU).hom (K.ideal V) hcenter b hb))) ≫
          GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a := by
  unfold GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart
  rw [Category.assoc, ← ComparisonChartPoint.Construction.globalBlowupMapTo_reesChart q I K hq hI hK U V hVU a b hb hcenter,
    ← Category.assoc, ← Spec.map_comp]
  rfl

theorem globalBlowupOverlapChart_map_right (q : Y ⟶ X)
    (I : X.IdealSheafData) (K : Y.IdealSheafData) (hq : I.comap q = K)
    (hI : I ≠ ⊥) (hK : K ≠ ⊥) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ q ⁻¹ᵁ U.1) (a : I.ideal U) (b c : K.ideal V)
    (hc : c.val = (q.appLE U.1 V.1 hVU).hom a.val)
    (hcenter : (I.ideal U).map (q.appLE U.1 V.1 hVU).hom = K.ideal V) :
    GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart K hK V b c ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK =
      Spec.map (CommRingCat.ofHom ((Blowup.ChartOverlap.Construction.blowupChartOverlapRight (K.ideal V) b c).comp
        (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo (I.ideal U) a (q.appLE U.1 V.1 hVU).hom (K.ideal V) hcenter c hc))) ≫
          GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a := by
  rw [GlobalBlowup.OverlapChart.Construction.globalBlowupOverlapChart_right, Category.assoc,
    ← ComparisonChartPoint.Construction.globalBlowupMapTo_reesChart q I K hq hI hK U V hVU a c hc hcenter,
    ← Category.assoc, ← Spec.map_comp]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.OverlapComparisonMaps.Construction
