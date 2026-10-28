import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.SectionProjectiveModuleChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Conormal.InfinityChartIdeal

/-! # Free Infinity Charts -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.FreeInfinityCharts.BundleCycles

noncomputable section

/-! The actual projective compactification of a smooth closed
section admits finite free infinity charts at every center point. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme.{0}} (p : Y ⟶ X) [Smooth p]
    (s : X ⟶ Y) [IsClosedImmersion s] (hs : s ≫ p = 𝟙 X)

include p hs in
theorem globalConormal_hasFreeInfinityCharts :
    Free.ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker)
      (InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker) := by
  intro x
  obtain ⟨U, hU, hfinite, hprojective⟩ := Global.SectionProjectiveModuleChart.BundleCycles.globalSection_exists_projectiveModuleChart p s hs x
  let R := Γ(Y, U.1) ⧸ s.ker.ideal U
  let M := (s.ker.ideal U).Cotangent
  let : Module.Finite R M := hfinite
  let : Module.Projective R M := hprojective
  obtain ⟨y, hy⟩ := hU
  obtain ⟨C⟩ := Free.InfinityChart.BundleCycles.projectiveModule_hasFreeInfinityCharts R M y
  let i : Spec (.of R) ⟶ s.ker.subscheme := Support.Projection.BundleCycles.supportCoefficientChart s.ker U
  let j : SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R (R × M) ⟶ Conormal.ProjectiveGluing.BundleCycles.globalConormalProjective s.ker :=
    (Conormal.ProjectiveGluing.BundleCycles.globalConormalProjectiveCover s.ker).f U
  let : IsOpenImmersion i := Support.Projection.BundleCycles.supportCoefficientChart_isOpenImmersion s.ker U
  let : IsOpenImmersion j := Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveCover_isOpenImmersion s.ker U
  have H := C.compOpen (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport s.ker) i j
    (Conormal.ProjectiveProper.BundleCycles.globalConormalProjectiveToSupport_chart_isPullback s.ker U)
    (InfinityBundle.Cycles.globalConormalInfinityIdealLineBundle s.ker) (Conormal.InfinityChartIdeal.BundleCycles.conormalInfinityChartIdealIso s.ker U)
  exact ⟨hy ▸ H⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalConormal.FreeInfinityCharts.BundleCycles
