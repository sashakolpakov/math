import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.AuxiliaryProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.HistoryProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.SameEtalePullbackExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.ControlPrefixOpenExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ResidualNeighborhoodBoundary

/-! # History Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension

noncomputable section

/-! Reconstruct the complete history schedule on an étale pullback, including its actual open continuations. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem HistoryProgramAuxiliary.Construction.DimensionHistoryProgram.exists_etale_pullback
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β γ : Type} [Fintype β] [Fintype γ] [DecidableEq β] {e : γ ↪ β}
    {schedule : HistoryProgramAuxiliary.Construction.DimensionHistorySchedule 𝒮 n e} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (H : HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule X f J D Y g K P) :
    ∀ [Smooth f] (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V],
      ∀ (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData), L ≠ ⊥ →
        ∀ (E : β → V.IdealSheafData) (q : V ⟶ X) [Etale q],
        q ≫ f = h → J.comap q = L → (∀ l, (D l).comap q = E l) →
        ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
          (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M) (r : W ⟶ Y),
          HistoryProgramAuxiliary.Construction.DimensionHistoryProgram 𝒮 n schedule V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  induction H with
  | full e he ℓ H =>
      intro _ V _ _ _ h L _ E q _ hstructure hL hD
      obtain ⟨W, k, M, Q, r, hQ, hc⟩ := H.exists_etale_pullback V h L E q hstructure hL hD
      exact ⟨W, k, M, Q, r, .full e he ℓ hQ, hc⟩
  | @clear β γ hβ hγ dec e j hj ℓ schedule X Y f hf g J C J' D A aux hA P same V Z h k L M T tail R r comparison hR hcover ih =>
      intro _ V0 _ _ _ h0 L0 hL0 E0 q _ hstructure hL hD
      let : Smooth h0 := hstructure ▸ inferInstanceAs (Smooth (q ≫ f))
      obtain ⟨Y0, g0, C0, A0, a, aux0, ha⟩ := aux.exists_etale_pullback V0 h0 L0 E0 q hstructure hL hD
      obtain ⟨J0, P0, same0, hp⟩ := same.exists_etale_pullback_transport A0 q a ha L0 hL
      let : Smooth g := A.endpoint_smooth
      let : Smooth g0 := A0.endpoint_smooth
      let : IsIntegral Y0 := A0.endpoint_integral
      let : IsLocallyNoetherian Y0 := LocallyOfFiniteType.isLocallyNoetherian g0
      let : CompactSpace Y0 := QuasiCompact.compactSpace_of_compactSpace A0.toBase
      let : IsNoetherian Y0 := ⟨⟩
      let : Etale a := (ha.endpoint_pullback A A0 q a).1
      have hg := ha.endpoint_structure A A0 q a
      have hJ0 := (hp.endpoint_pullback P P0 q a).2.2
      have hA0 := ha.uniformBoundaryCompatible A A0 q a β D hA
      rw [funext hD] at hA0
      have hAB0 := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible A0 E0 hA0
      let N := ℓ.stepCount
      let EA0 := Classical.choice (A0.boundaryAtLength_atlas E0 hAB0 N aux0.stepCount)
      let U0 := A0.transformedBoundaryComplement E0 j
      have hboundaryNonzero : A0.transformIdeal (E0 j) 1 ≠ ⊥ := by
        rw [← A0.boundaryAtLength_initialLabel E0 j N aux0.stepCount]
        exact EA0.component_ne_bot _
      let : Nonempty U0 := by
        obtain ⟨x, hx⟩ := GlobalBlowup.Local.Construction.idealSheaf_supportComplement_nonempty _ hboundaryNonzero
        exact ⟨⟨x, hx⟩⟩
      let : IsIntegral U0 := isIntegral_of_isOpenImmersion U0.ι
      let : IsLocallyNoetherian U0 := LocallyOfFiniteType.isLocallyNoetherian U0.ι
      let : NoetherianSpace U0 := U0.ι.isOpenEmbedding.isInducing.noetherianSpace
      have hJ0ne : J0 ≠ ⊥ := P0.endpoint_ideal_ne_bot hL0
      have hJU0 : J0.comap U0.ι ≠ ⊥ := Global.ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot U0.ι J0 hJ0ne
      have hboundary := ha.boundaryAtLength A A0 q a β D E0 hD N aux.stepCount aux0.stepCount
      obtain ⟨u, hu, hpb⟩ := ha.exists_transformed_boundary_complement_pullback A A0 q a D E0 hD j
      let : Etale u := hu
      obtain ⟨V1, h1, L1, T0, v, tail0, hv⟩ := ih U0 (U0.ι ≫ g0) (J0.comap U0.ι) hJU0
        (fun l => (A0.boundaryAtLength E0 N aux0.stepCount l).comap U0.ι) u
        (by rw [← Category.assoc, hpb.w, Category.assoc, hg])
        (by rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, hJ0])
        (by
          intro l
          rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, congrFun hboundary l])
      have hclear := A0.auxiliary_clearance (Nat.succ_pos n) L0 (E0 j) rfl
        (by simpa only [Nat.add_sub_cancel, Nat.succ_sub_one] using aux0.terminal_order)
      rw [same0.transformIdeal] at hclear
      have hstart : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g0 J0 n).support : Set Y0) ⊆ Set.range U0.ι :=
        Global.ClearedHistoryNeighborhood.Construction.cleared_boundary_complement_contains_order_locus g0 J0 (A0.transformIdeal (E0 j) 1) (n + 1) hclear
      obtain ⟨Z0, k0, M0, R0, r0, hR0, comparison0, _, hremaining⟩ :=
        T0.exists_uniform_extension_from_order_neighborhood Y0 g0 J0 hJ0ne U0.ι rfl rfl
          (by simpa only [Nat.add_sub_cancel] using hstart) (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels N β)
          (A0.boundaryAtLength E0 N aux0.stepCount) EA0 tail0.uniformBoundaryCompatible
      have hcombined := comparison.comp R T _ r T0 u v hv
      have hcombined' : R.EtaleComparison T0 (U0.ι ≫ a) (v ≫ r) := by
        rw [← hpb.w]
        exact hcombined
      obtain ⟨s, hs⟩ := R.exists_etaleComparison_of_order_neighborhood R0 a hg hJ0 T0
        U0.ι (v ≫ r) r0 hcombined' comparison0 (by simpa only [Nat.add_sub_cancel] using hstart)
      exact ⟨Z0, k0, M0, P0.append R0, s,
        .clear e j hj ℓ schedule A0 aux0 hA0 P0 same0 T0 tail0 R0 r0 comparison0 hR0
          (by simpa only [Nat.add_sub_cancel] using hremaining),
        hp.append P P0 q a R R0 s hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension
