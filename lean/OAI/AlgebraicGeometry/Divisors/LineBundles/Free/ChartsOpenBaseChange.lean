import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChart
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityChartOpenLift
import OAI.AlgebraicGeometry.Divisors.LineBundles.Free.InfinityCharts

/-! # Charts Open Base Change -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsOpenBaseChange.BundleCycles

noncomputable section

/-! Actual free infinity charts persist under open base change,
including a rank specified only along that open base. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {E X U : Scheme.{0}} (p : E ⟶ X) (L : LineBundles.Scheme.SchemeIdealModule.BundleCycles.SchemeLineBundle E)
    (i : U ⟶ X) [IsOpenImmersion i]

theorem freeInfinityCharts_openBaseChange (H : ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts p L) :
    ProjectiveInfinityChart.BundleCycles.HasFreeProjectiveInfinityCharts (pullback.snd p i) (L.pullback (pullback.fst p i)) := by
  intro x
  obtain ⟨C⟩ := H (i x)
  obtain ⟨D, _, hD⟩ := C.refineOpen i.opensRange ⟨x, rfl⟩
  exact ⟨D.openLift i x hD⟩

theorem freeInfinityCharts_openBaseChange_of_rank (r : ℕ)
    (H : ∀ x : U, ∃ C : ProjectiveInfinityChart.BundleCycles.FreeProjectiveInfinityChart p L (i x), C.rank = r) :
    InfinityCharts.BundleCycles.HasFreeProjectiveInfinityChartsOfRank (pullback.snd p i) (L.pullback (pullback.fst p i)) r := by
  intro x
  obtain ⟨C, hC⟩ := H x
  obtain ⟨D, hDC, hD⟩ := C.refineOpen i.opensRange ⟨x, rfl⟩
  exact ⟨D.openLift i x hD, (D.openLift_rank i x hD).trans (hDC.trans hC)⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Free.ChartsOpenBaseChange.BundleCycles
