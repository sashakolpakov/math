import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CoordinateSubspaceChartExistence

/-! # Coordinate Subspace Cover -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CoordinateSubspaceCover.Construction

noncomputable section

/-! Compactness gives a finite retained coordinate-model cover of a smooth closed carrier. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_global_coordinate_subspace_cover
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    [Smooth (J.subschemeι ≫ f)] :
    ∃ (s : Finset {x : X // x ∈ J.support}) (C : ∀ i : s, Global.CoordinateSubspaceChart.Construction.GlobalCoordinateSubspaceChart f J i.val.val),
      ∀ x ∈ J.support, ∃ i p, (C i).map p = x := by
  classical
  let P := {x : X // x ∈ J.support}
  let C (x : P) := Classical.choice (Global.CoordinateSubspaceChartExistence.Construction.exists_global_coordinate_subspace_chart f J hJ x.val x.property)
  have hcover : (J.support : Set X) ⊆ ⋃ x : P, ((C x).map.opensRange : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (C ⟨x, hx⟩).point, (C ⟨x, hx⟩).point_over⟩
  obtain ⟨s, hs⟩ := J.support.isClosed.isCompact.elim_finite_subcover
    (fun x : P => ((C x).map.opensRange : Set X)) (fun x => (C x).map.opensRange.isOpen) hcover
  refine ⟨s, fun i => C i.val, ?_⟩
  intro x hx
  obtain ⟨i, hi, p, hp⟩ := Set.mem_iUnion₂.mp (hs hx)
  exact ⟨⟨i, hi⟩, p, hp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Finite.CoordinateSubspaceCover.Construction
