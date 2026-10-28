import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.SpecifiedMap
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBlowup.FunctorialMap
import OAI.AlgebraicGeometry.Resolution.Blowups.SpecifiedBlowupChart
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Comparison Chart Point -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global.ComparisonChartPoint.Construction

noncomputable section

section

/-! The actual global blowup maps restrict to the explicitly specified denominator maps. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

theorem globalBlowupMapTo_reesChart (q : Y ⟶ X)
    (I : X.IdealSheafData) (K : Y.IdealSheafData) (hq : I.comap q = K)
    (hI : I ≠ ⊥) (hK : K ≠ ⊥) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ q ⁻¹ᵁ U.1) (a : I.ideal U) (b : K.ideal V)
    (hb : b.val = (q.appLE U.1 V.1 hVU).hom a.val)
    (hcenter : (I.ideal U).map (q.appLE U.1 V.1 hVU).hom = K.ideal V) :
    Spec.map (CommRingCat.ofHom
        (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo (I.ideal U) a (q.appLE U.1 V.1 hVU).hom (K.ideal V) hcenter b hb)) ≫
        GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a =
      GlobalControlled.Chart.Construction.globalBlowupReesChart K hK V b ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK := by
  subst K
  change _ = GlobalControlled.Chart.Construction.globalBlowupReesChart (I.comap q) hK V b ≫ GlobalBlowup.FunctorialMap.Construction.globalBlowupMap q I hI hK
  unfold GlobalControlled.Chart.Construction.globalBlowupReesChart
  rw [Category.assoc, GlobalBlowup.FunctorialMap.Construction.globalBlowupMap_chart q I hI hK U V hVU,
    ← Category.assoc, SpecifiedBlowupChart.Construction.affineBlowupMapTo_chart]
  exact Category.assoc _ _ _

end

/-! Lift an actual point of a global comparison to the matching denominator chart over a chosen affine neighborhood. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X Y : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
  [IsIntegral Y] [IsLocallyNoetherian Y]

theorem globalBlowupMapTo_chart (q : Y ⟶ X)
    (I : X.IdealSheafData) (K : Y.IdealSheafData) (hq : I.comap q = K)
    (hI : I ≠ ⊥) (hK : K ≠ ⊥) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ q ⁻¹ᵁ U.1)
    (hcenter : (I.ideal U).map (q.appLE U.1 V.1 hVU).hom = K.ideal V) :
    GlobalBlowup.Data.Construction.globalBlowupChart K hK V ≫ GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK =
      Blowup.Functor.Construction.affineBlowupMapTo (I.ideal U) (K.ideal V) (q.appLE U.1 V.1 hVU).hom hcenter ≫
        GlobalBlowup.Data.Construction.globalBlowupChart I hI U := by
  subst K
  exact GlobalBlowup.FunctorialMap.Construction.globalBlowupMap_chart q I hI hK U V hVU

theorem exists_globalBlowupMapTo_reesChart_point (q : Y ⟶ X)
    (I : X.IdealSheafData) (K : Y.IdealSheafData) (hq : I.comap q = K)
    (hI : I ≠ ⊥) (hK : K ≠ ⊥) (U : X.affineOpens) (V : Y.affineOpens)
    (hVU : V.1 ≤ q ⁻¹ᵁ U.1) (a : I.ideal U) (b : K.ideal V)
    (hb : b.val = (q.appLE U.1 V.1 hVU).hom a.val)
    (hcenter : (I.ideal U).map (q.appLE U.1 V.1 hVU).hom = K.ideal V)
    (x : GlobalBlowup.Data.Construction.globalBlowup K hK) (hx : GlobalBlowup.Data.Construction.globalBlowupToBase K hK x ∈ V.1)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (I.ideal U) a))
    (hp : GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK x = GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a p) :
    ∃ Q : PrimeSpectrum (Blowup.Charts.Construction.blowupChart (K.ideal V) b),
      GlobalControlled.Chart.Construction.globalBlowupReesChart K hK V b Q = x ∧
        PrimeSpectrum.comap
          (Blowup.ChartSpecifiedMap.Construction.blowupChartMapTo (I.ideal U) a (q.appLE U.1 V.1 hVU).hom (K.ideal V) hcenter b hb) Q = p := by
  have hrange : x ∈ (GlobalBlowup.Data.Construction.globalBlowupChart K hK V).opensRange := by
    rw [GlobalBlowup.MapGluing.Construction.globalBlowupChart_opensRange]
    exact hx
  obtain ⟨z, hz⟩ := hrange
  let φ := (q.appLE U.1 V.1 hVU).hom
  let A := Blowup.Functor.Construction.affineBlowupMapTo (I.ideal U) (K.ideal V) φ hcenter
  let j := Proj.awayι (ReesGrading.Construction.reesGrade (I.ideal U)) (Blowup.Charts.Construction.reesGenerator (I.ideal U) a)
    (Blowup.Charts.Construction.reesGenerator_mem (I.ideal U) a) (by decide)
  have he : A z = j p := by
    apply (GlobalBlowup.Data.Construction.globalBlowupChart I hI U).isOpenEmbedding.injective
    calc
      _ = GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I K hq hI hK (GlobalBlowup.Data.Construction.globalBlowupChart K hK V z) :=
        (congrArg (fun m => m z) (globalBlowupMapTo_chart q I K hq hI hK U V hVU hcenter)).symm
      _ = GlobalControlled.Chart.Construction.globalBlowupReesChart I hI U a p := by rw [hz, hp]
      _ = _ := rfl
  obtain ⟨Q, hQp, hQz⟩ := Scheme.exists_preimage_of_isPullback
    (SpecifiedBlowupChart.Construction.affineBlowupMapTo_chart_isPullback (I.ideal U) a φ (K.ideal V) hcenter b hb) p z he.symm
  refine ⟨Q, ?_, hQp⟩
  exact (congrArg (GlobalBlowup.Data.Construction.globalBlowupChart K hK V) hQz).trans hz

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global.ComparisonChartPoint.Construction
