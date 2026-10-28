import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.HistoryFiniteExistence

/-! # Order Finite Programs -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface.OrderFinitePrograms.Construction

noncomputable section

/-! Ordinary maximum-order surface problems in a finite family have one common complete history schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_finite_surface_history_programs
    (n : ℕ) {β γ ι : Type} [Fintype β] [Fintype γ] [DecidableEq β] [Fintype ι] (e : γ ↪ β)
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ 2)
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (G : ∀ i, GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (f i) (D i))
    (hbound : ∀ i, ((G i).reindex e).logarithmicIdeal (J i) (n + 1) = ⊤) :
    ∃ schedule : HistorySchedule.Construction.SurfaceHistorySchedule n e, ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        HistoryProgram.Construction.SurfaceHistoryProgram n schedule (X i) (f i) (J i) (D i) Y g K P :=
  HistoryFiniteExistence.Construction.exists_finite_surface_history_programs_of_count n (Fintype.card β - Fintype.card γ) e le_rfl
    X f J hJ hd D E G hbound

theorem exists_finite_surface_order_programs
    (n : ℕ) {β ι : Type} [Fintype β] [DecidableEq β] [Fintype ι]
    (X : ι → Scheme) [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, CompactSpace (X i)]
    (f : ∀ i, X i ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [∀ i, Smooth (f i)] (J : ∀ i, (X i).IdealSheafData)
    (hJ : ∀ i, J i ≠ ⊥) (hd : ∀ i, topologicalKrullDim (X i) ≤ 2)
    (D : ∀ i, β → (X i).IdealSheafData)
    (E : ∀ i, Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (f i) (D i) [Finset.univ])
    (hbound : ∀ i, Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (f i) (J i) (n + 1) = ⊤) :
    ∃ schedule : HistorySchedule.Construction.SurfaceHistorySchedule n (Function.Embedding.ofIsEmpty : Fin 0 ↪ β), ∀ i,
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) (X i) (f i) (J i) Y g K),
        HistoryProgram.Construction.SurfaceHistoryProgram n schedule (X i) (f i) (J i) (D i) Y g K P := by
  classical
  let G (i : ι) := Classical.choice (E i).exists_modelAtlas
  apply exists_finite_surface_history_programs n Function.Embedding.ofIsEmpty X f J hJ hd D E G
  intro i
  rw [GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmicIdeal_empty]
  exact hbound i

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface.OrderFinitePrograms.Construction
