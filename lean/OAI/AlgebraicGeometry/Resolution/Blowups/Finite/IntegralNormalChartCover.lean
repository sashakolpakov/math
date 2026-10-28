import OAI.AlgebraicGeometry.Resolution.Blowups.Integral.ModeledNormalChart
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.NormalChartIntrinsicData

/-! # Integral Normal Chart Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.IntegralNormalChartCover.Construction

noncomputable section

/-! Compactness gives a finite integral modeled normal-chart cover of the whole order locus. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_integral_global_normal_chart_cover
    {X : Scheme} [CompactSpace X] {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {β : Type} [Fintype β] {D : β → X.IdealSheafData}
    (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (J : X.IdealSheafData) (n : ℕ)
    (hbound : B.logarithmicIdeal J (n + 1) = ⊤) :
    ∃ (s : Finset {x : X // x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support})
      (C : ∀ i : s, GlobalBoundary.ModeledNormalChart.Construction.GlobalBoundaryModeledNormalChart f J n D i.val.val),
      (∀ i, IsDomain (C i).chart.ring) ∧
      (∀ i, IsIntegral (C i).chart.nativeCarrier.subscheme) ∧
      ∀ x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support, ∃ i p, (C i).chart.map p = x := by
  classical
  let P := {x : X // x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support}
  have hex (x : P) := Integral.ModeledNormalChart.Construction.exists_integral_global_boundary_modeled_normal_chart B J n hbound x.val x.property
  choose C hR hH using hex
  have hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support : Set X) ⊆
      ⋃ x : P, ((C x).chart.map.opensRange : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (C ⟨x, hx⟩).chart.point, (C ⟨x, hx⟩).chart.point_over⟩
  obtain ⟨s, hs⟩ := (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support.isClosed.isCompact.elim_finite_subcover
    (fun x : P => ((C x).chart.map.opensRange : Set X))
    (fun x => (C x).chart.map.opensRange.isOpen) hcover
  refine ⟨s, fun i => C i.val, fun i => hR i.val, fun i => hH i.val, ?_⟩
  intro x hx
  obtain ⟨i, hi, p, hp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact ⟨⟨i, hi⟩, p, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.IntegralNormalChartCover.Construction
