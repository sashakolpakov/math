import OAI.AlgebraicGeometry.Resolution.Blowups.DimensionOrderProgramPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.MonomialProgramEtalePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.ResidualProgramNaturality
import OAI.AlgebraicGeometry.Resolution.Blowups.SameEtalePullbackExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.Ideal.ComplementEtalePullback

/-! # Residual Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension

noncomputable section

/-! Complete residual schedules pull back étale, including all controls and the actual residual-neighborhood extensions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem ResidualFinite.Construction.DimensionResidualProgram.exists_etale_pullback {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {b : ℕ} (hb : 0 < b)
    {m : ℕ} {β : Type} [Fintype β] [DecidableEq β] {a : β → ℕ}
    {schedule : ResidualFinite.Construction.DimensionResidualSchedule 𝒮 b m β a} {X Y : Scheme}
    {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : ResidualFinite.Construction.DimensionResidualProgram 𝒮 b schedule X f J I D Y g K P) :
    ∀ [Smooth f] (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V],
      topologicalKrullDim V ≤ (d + 1 : ℕ) → ∀ (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L B : V.IdealSheafData), L ≠ ⊥ → B ≠ ⊥ →
        ∀ (E : β → V.IdealSheafData) (q : V ⟶ X) [Etale q],
        q ≫ f = h → J.comap q = L → I.comap q = B → (∀ l, (D l).comap q = E l) →
        ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
          (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h B W k M) (r : W ⟶ Y),
          ResidualFinite.Construction.DimensionResidualProgram 𝒮 b schedule V h L B E W k M Q ∧ P.EtaleComparison Q q r := by
  induction H with
  | monomial a S H =>
      intro _ V _ _ _ _ h L B _ _ E q _ hstructure _ hB hD
      obtain ⟨W, k, M, Q, r, hQ, hc⟩ := H.exists_etale_pullback hb V h B E q hstructure hB hD
      exact ⟨W, k, M, Q, r, .monomial a S hQ, hc⟩
  | @higher m β hβ dec a hle S schedule X Y Z f hf g h J I J' I' K D A order P same R tail ih =>
      intro _ V0 _ _ _ hdV0 h0 L0 B0 hL0 hB0 E0 q _ hstructure hL hB hD
      let : Smooth h0 := hstructure ▸ inferInstanceAs (Smooth (q ≫ f))
      obtain ⟨Y0, g0, J0, A0, u, order0, ha⟩ := order.exists_etale_pullback V0 h0 L0 hL0 E0 q hstructure hL hD
      obtain ⟨I0, P0, same0, hp⟩ := same.exists_etale_pullback_transport A0 q u ha B0 hB
      let : Smooth g := A.endpoint_smooth
      let : Smooth g0 := A0.endpoint_smooth
      let : IsIntegral Y0 := A0.endpoint_integral
      let : IsLocallyNoetherian Y0 := LocallyOfFiniteType.isLocallyNoetherian g0
      let : CompactSpace Y0 := QuasiCompact.compactSpace_of_compactSpace A0.toBase
      let : Etale u := (ha.endpoint_pullback A A0 q u).1
      have hg := ha.endpoint_structure A A0 q u
      have hJ0 := (ha.endpoint_pullback A A0 q u).2.2
      have hI0 := (hp.endpoint_pullback P P0 q u).2.2
      have hcount := order.hasIncidenceTrace.stepCount A D S.incidenceTrace
      have hcount0 := order0.hasIncidenceTrace.stepCount A0 E0 S.incidenceTrace
      have hboundary := ha.boundaryAtLength A A0 q u β D E0 hD S.incidenceTrace.length hcount hcount0
      obtain ⟨W, k0, M0, R0, r0, tail0, hr⟩ := ih Y0 (A0.endpoint_dimension_le (d + 1) hdV0) g0 J0 I0
        (A0.endpoint_ideal_ne_bot hL0) (P0.endpoint_ideal_ne_bot hB0)
        (A0.boundaryAtLength E0 S.incidenceTrace.length hcount0) u hg hJ0 hI0
        (fun l => congrFun hboundary l)
      exact ⟨W, k0, M0, P0.append R0, r0,
        .higher a hle S schedule A0 order0 P0 same0 R0 tail0, hp.append P P0 q u R R0 r0 hr⟩
  | @companion m β hβ dec a hlt S schedule X Y f hf g hgs J I C J' I' D A order B sameB P same V Z h k L M T tail R r comparison hstart hcover ih =>
      intro _ V0 _ _ _ hdV0 h0 L0 B0 hL0 hB0 E0 q _ hstructure hL hB hD
      let : Smooth h0 := hstructure ▸ inferInstanceAs (Smooth (q ≫ f))
      let C0 := Global.CompanionIdeal.Construction.globalCompanionIdeal L0 (Global.MixedBoundary.Construction.boundaryMonomialSheaf E0 a) (m + 1) b
      have hC0 : C0 ≠ ⊥ := by
        intro hz
        have hle : L0 ^ (b - (m + 1)) ≤ C0 := le_sup_left
        rw [hz] at hle
        exact Integral.IdealSheafProducts.Construction.idealSheaf_pow_ne_bot L0 hL0 _ (le_bot_iff.mp hle)
      have hCmap : (Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b).comap q = C0 := by
        rw [Global.CompanionIdeal.Construction.globalCompanionIdeal_comap, hL, ResidualNeighborhoodEtalePullback.Construction.boundaryMonomialSheaf_comap, funext hD]
      obtain ⟨Y0, g0, K0, A0, u, order0, ha⟩ := order.exists_etale_pullback V0 h0 C0 hC0 E0 q hstructure hCmap hD
      obtain ⟨J0, B1, sameB0, hbcomp⟩ := sameB.exists_etale_pullback_transport A0 q u ha L0 hL
      obtain ⟨I0, P0, same0, hp⟩ := same.exists_etale_pullback_transport A0 q u ha B0 hB
      let : Smooth g0 := A0.endpoint_smooth
      let : IsIntegral Y0 := A0.endpoint_integral
      let : IsLocallyNoetherian Y0 := LocallyOfFiniteType.isLocallyNoetherian g0
      let : CompactSpace Y0 := QuasiCompact.compactSpace_of_compactSpace A0.toBase
      let : IsNoetherian Y0 := ⟨⟩
      let : Etale u := (ha.endpoint_pullback A A0 q u).1
      have hg := ha.endpoint_structure A A0 q u
      have hJ0 := (hbcomp.endpoint_pullback B B1 q u).2.2
      have hI0 := (hp.endpoint_pullback P P0 q u).2.2
      have hJ0ne : J0 ≠ ⊥ := B1.endpoint_ideal_ne_bot hL0
      have hI0ne : I0 ≠ ⊥ := P0.endpoint_ideal_ne_bot hB0
      have hcount := order.hasIncidenceTrace.stepCount A D S.incidenceTrace
      have hcount0 := order0.hasIncidenceTrace.stepCount A0 E0 S.incidenceTrace
      have hboundary := ha.boundaryAtLength A A0 q u β D E0 hD S.incidenceTrace.length hcount hcount0
      have hA0 := order0.hasIncidenceTrace.uniformBoundaryCompatible A0 E0 S.incidenceTrace
      have hAB0 := Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix.uniformBoundaryCompatible.boundaryCompatible A0 E0 hA0
      let EA0 := Classical.choice (A0.boundaryAtLength_atlas E0 hAB0 S.incidenceTrace.length hcount0)
      let U0 := Global.ResidualNeighborhood.Construction.residualOrderDropOpen g0 J0 (m + 1)
      let : IsIntegral U0 := Global.ResidualNeighborhood.Construction.residualOrderDropOpen_integral g0 J0 hJ0ne (m + 1)
      let : IsLocallyNoetherian U0 := LocallyOfFiniteType.isLocallyNoetherian U0.ι
      let : NoetherianSpace U0 := U0.ι.isOpenEmbedding.isInducing.noetherianSpace
      have hdU0 : topologicalKrullDim U0 ≤ (d + 1 : ℕ) :=
        U0.ι.isOpenEmbedding.isInducing.topologicalKrullDim_le.trans (A0.endpoint_dimension_le (d + 1) hdV0)
      obtain ⟨v, hv, hpb⟩ := ResidualNeighborhoodEtalePullback.Construction.exists_residual_order_neighborhood_etale_pullback g g0 J' J0 (m + 1) u hg hJ0
      let : Etale v := hv
      obtain ⟨V1, h1, L1, T0, w, tail0, ht⟩ := ih U0 hdU0 (U0.ι ≫ g0) (J0.comap U0.ι) (I0.comap U0.ι)
        (Global.ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot U0.ι J0 hJ0ne)
        (Global.ResidualNeighborhoodBoundary.Construction.idealSheaf_comap_nonempty_open_ne_bot U0.ι I0 hI0ne)
        (fun l => (A0.boundaryAtLength E0 S.incidenceTrace.length hcount0 l).comap U0.ι) v
        (by rw [← Category.assoc, hpb.w, Category.assoc, hg])
        (by rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, hJ0])
        (by rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, hI0])
        (by
          intro l
          rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, congrFun hboundary l])
      have hdiff : (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g I' (b - 1)).comap u =
          Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g0 I0 (b - 1) := by
        rw [Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, hI0]
        exact DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr _ _ hg _ _
      have hstart0 : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g0 I0 (b - 1)).support : Set Y0) ⊆ Set.range U0.ι :=
        Ideal.ComplementEtalePullback.Construction.idealSheaf_support_cover_pullback u (Global.ResidualNeighborhood.Construction.residualOrderDropOpen g J' (m + 1)).ι U0.ι v hpb _ _ hdiff hstart
      obtain ⟨Z0, k0, M0, R0, r0, hR0, comparison0, _, hremaining⟩ :=
        T0.exists_uniform_extension_from_order_neighborhood Y0 g0 I0 hI0ne U0.ι rfl rfl hstart0
          (ControlPrefix.CanonicalLabels.Construction.iteratedBoundaryLabels S.incidenceTrace.length β)
          (A0.boundaryAtLength E0 S.incidenceTrace.length hcount0) EA0 tail0.uniformBoundaryCompatible
      have hcombined := comparison.comp R T _ r T0 v w ht
      have hcombined' : R.EtaleComparison T0 (U0.ι ≫ u) (w ≫ r) := by
        rw [← hpb.w]
        exact hcombined
      obtain ⟨s, hs⟩ := R.exists_etaleComparison_of_order_neighborhood R0 u hg hI0 T0
        U0.ι (w ≫ r) r0 hcombined' comparison0 hstart0
      exact ⟨Z0, k0, M0, P0.append R0, s,
        .companion a hlt S schedule A0 order0 B1 sameB0 P0 same0 T0 tail0 R0 r0 comparison0 hstart0 hremaining,
        hp.append P P0 q u R R0 s hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension
