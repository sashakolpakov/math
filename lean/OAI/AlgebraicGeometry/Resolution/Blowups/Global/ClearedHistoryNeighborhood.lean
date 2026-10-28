import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UnitHistoryExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.OrderSequenceExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhood

/-! # Cleared History Neighborhood -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Cleared boundary complements contain the full order locus and allow one more old label in the history. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas.logarithmic_bound_extend_history_on_open
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {β γ : Type} {D : β → X.IdealSheafData}
    (A : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas f D) (e : γ ↪ β) (j : β) (hj : ∀ s, j ≠ e s)
    (J : X.IdealSheafData) (n : ℕ) (hbound : (A.reindex e).logarithmicIdeal J n = ⊤)
    (U : X.Opens) (hunit : (D j).comap U.ι = ⊤)
    (B : GlobalBoundary.ModelAtlas.Construction.GlobalBoundaryModelAtlas (U.ι ≫ f) (fun l => (D l).comap U.ι)) :
    (B.reindex (Finite.BoundaryHistoryExtension.Construction.extendSelectedBoundaryHistory e j hj)).logarithmicIdeal (J.comap U.ι) n = ⊤ := by
  rw [B.logarithmicIdeal_extend_unit_history e j hj hunit]
  rw [← (A.reindex e).logarithmicIdeal_comap_etale U.ι (B.reindex e), hbound,
    Scheme.IdealSheafData.comap_top]

theorem Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J L : X.IdealSheafData) (m : ℕ)
    (hclear : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) ⊔ L = ⊤) :
    ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1)).support : Set X) ⊆
      Set.range (Scheme.Opens.ι (X := X) L.support.compl) := by
  intro x hx
  exact ⟨⟨x, Global.ResidualNeighborhood.Construction.idealSheaf_support_subset_complement_of_sup_top _ _ hclear hx⟩, rfl⟩

theorem Global.ClearedHistoryNeighborhood.Construction.exists_boundary_integral_sequence_of_cleared_component
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J L : X.IdealSheafData) (hJ : J ≠ ⊥) (m : ℕ)
    (hclear : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) ⊔ L = ⊤)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence m L.support.compl
      (Scheme.Opens.ι (X := X) L.support.compl ≫ f)
      (J.comap (Scheme.Opens.ι (X := X) L.support.compl)))
    (hT : T.integralCenters)
    (hTB : T.boundaryCompatible β (fun l => (D l).comap (Scheme.Opens.ι (X := X) L.support.compl))) :
    ∃ S : Global.MonomialSequence.Construction.SmoothFixedControlSequence m X f J, S.integralCenters ∧ S.boundaryCompatible β D :=
  T.extend_boundary_integral_from_order_neighborhood X f J hJ
    (Scheme.Opens.ι (X := X) L.support.compl) rfl rfl
    (Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus f J L m hclear) β D A hT hTB

end

end OAI.AlgebraicGeometry.Resolution.Blowups
