import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalControlled.Chart
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.OverlapGlobalIntersection

/-! # Overlap Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OverlapChart.Construction

noncomputable section

/-! Actual common denominator neighborhoods inside a global blowup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

def globalBlowupOverlapChart (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a b : I.ideal U) :
    Spec (.of (Blowup.ChartOverlap.Construction.blowupChartOverlap (I.ideal U) a b)) ⟶ Data.Construction.globalBlowup I hI :=
  Spec.map (CommRingCat.ofHom (Blowup.ChartOverlap.Construction.blowupChartOverlapLeft (I.ideal U) a b)) ≫
    GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a

instance globalBlowupOverlapChart_isOpenImmersion (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a b : I.ideal U) : IsOpenImmersion (globalBlowupOverlapChart I hI U a b) := by
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom (Blowup.ChartOverlap.Construction.blowupChartOverlapLeft (I.ideal U) a b))) :=
    Blowup.ChartOverlap.Construction.blowupChartOverlapLeft_isOpenImmersion (I.ideal U) a b
  unfold globalBlowupOverlapChart
  infer_instance

theorem globalBlowupOverlapChart_right (I : X.IdealSheafData) (hI : I ≠ ⊥)
    (U : X.affineOpens) (a b : I.ideal U) :
    globalBlowupOverlapChart I hI U a b =
      Spec.map (CommRingCat.ofHom (Blowup.ChartOverlap.Construction.blowupChartOverlapRight (I.ideal U) a b)) ≫
        GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U b := by
  unfold globalBlowupOverlapChart GlobalControlled.Chart.Construction.globalBlowupReesChart
  rw [← Category.assoc, Blowup.OverlapGlobalIntersection.Construction.blowupChartOverlap_global_commutes, Category.assoc]

end

end OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.OverlapChart.Construction
