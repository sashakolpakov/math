import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramAuxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ComplementEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.SameEtalePullbackExistence

/-! # History Program Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension

noncomputable section

/-! Programs following one common dimension-indexed history schedule compare at every actual blowup step. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.exists_etaleComparison
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P) :
    ∀ [Smooth f] {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData} {E : β → V.IdealSheafData}
      {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M},
      HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule V h L E W k M Q →
      ∀ (q : V ⟶ X) [Etale q], q ≫ f = h → J.comap q = L → (∀ l, (D l).comap q = E l) →
      ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  induction T with
  | full e he ℓ T =>
      intro _ V W h _ k L M E Q S q _ hstructure hJ hD
      cases S with
      | full e he ℓ S => exact T.exists_etaleComparison S q hstructure hJ hD
  | clear e j hj ℓ schedule A aux hA P same T tail R r comparison hR hcover ih =>
      intro _ V W h _ k L M E Q S q _ hstructure hJ hD
      cases S with
      | clear e j hj ℓ schedule A' aux' hA' P' same' T' tail' R' r' comparison' hR' hcover' =>
          let _ := A.endpoint_smooth
          let _ := A'.endpoint_smooth
          obtain ⟨a, ha⟩ := aux.exists_etaleComparison aux' q hstructure hJ hD
          have hp := same.etaleComparison same' q a ha hJ
          let : Etale a := (ha.endpoint_pullback A A' q a).1
          have hg := ha.endpoint_structure A A' q a
          have hK := (hp.endpoint_pullback P P' q a).2.2
          have hboundary := ha.boundaryAtLength A A' q a _ _ _ hD _ aux.stepCount aux'.stepCount
          obtain ⟨u, hu, hpb⟩ := ha.exists_transformed_boundary_complement_pullback A A' q a _ _ hD j
          let : Etale u := hu
          obtain ⟨v, hv⟩ := ih tail' u
            (by rw [← Category.assoc, hpb.w, Category.assoc, hg])
            (by rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, hK])
            (by
              intro l
              rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, congrFun hboundary l])
          have hcombined := comparison.comp R T _ r T' u v hv
          have hcombined' : R.EtaleComparison T' ((A'.transformedBoundaryComplement E j).ι ≫ a) (v ≫ r) := by
            rw [← hpb.w]
            exact hcombined
          have hclear := A'.auxiliary_clearance (Nat.succ_pos n) L (E j) rfl
            (by simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using aux'.terminal_order)
          rw [same'.transformIdeal] at hclear
          obtain ⟨s, hs⟩ := R.exists_etaleComparison_of_order_neighborhood R' a hg hK T'
            (A'.transformedBoundaryComplement E j).ι (v ≫ r) r' hcombined' comparison'
            (by
              exact Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus
                _ _ (A'.transformIdeal (E j) 1) (n + 1) hclear)
          exact ⟨s, hp.append P P' q a R R' s hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension
