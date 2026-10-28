import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.BoundedChoicePullback
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.EtaleDataPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.EtalePullbackExistence
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.Bounds

/-! # Surface Program Etale Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Construct the complete prescribed-level surface program on an étale pullback, retaining every actual comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram.exists_etale_pullback
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (H : IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P) :
    ∀ [Smooth f] (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V],
      topologicalKrullDim V ≤ 2 → ∀ (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData)
        (E : β → V.IdealSheafData) (q : V ⟶ X) [Etale q],
        q ≫ f = h → J.comap q = L → (∀ l, (D l).comap q = E l) →
        ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
          (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M) (r : W ⟶ Y),
          IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  induction H with
  | @terminal m β hβ X f hf J D hstop A ht =>
      intro _ V _ _ _ _ h L E q _ hstructure hL hD
      subst h
      subst L
      have he : (fun l => (D l).comap q) = E := funext hD
      subst E
      have ht' : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) n = ⊤ := by
        rw [← Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, ht, Scheme.IdealSheafData.comap_top]
      exact ⟨V, q ≫ f, J.comap q, .stop, q, .terminal hstop (A.comapEtale f q) ht',
        inferInstance, rfl, rfl, rfl⟩
  | @refine ℓ β hβ X hX hNX hCX f J D A hb hd hlevel AM Y Z g k K M P hcenters hcount hP Q tail ih =>
      intro _ V _ _ _ hdV h L E q _ hstructure hL hD
      subst h
      subst L
      have he : (fun l => (D l).comap q) = E := funext hD
      subst E
      obtain ⟨B, hbB⟩ := A.exists_bounded_etale_pullback (ℓ + 1) hb q
      let hdB := B.chart_dimension_le 2 hdV
      have hcenter := A.surfaceCenter_comap_etale ℓ hb hd hlevel q B hbB hdB
      let BM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (q ≫ f) (B.surfaceCenter ℓ hbB hdB hlevel)
          (fun l => (D l).comap q) := by
        rw [← hcenter]
        exact AM.comapEtale f q
      obtain ⟨V', h', L', P', r, hc⟩ := P.exists_etale_pullback V (q ≫ f) (J.comap q) q rfl rfl
      let : Smooth g := P.endpoint_smooth
      let : Smooth h' := P'.endpoint_smooth
      let : IsIntegral V' := P'.endpoint_integral
      let : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian h'
      let : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace P'.toBase
      obtain ⟨hr, _, hK⟩ := hc.endpoint_pullback P P' q r
      let : Etale r := hr
      have hrstructure := hc.endpoint_structure P P' q r
      have hcount' : P'.stepCount = Fintype.card (Finset β) := (hc.stepCount_eq P P' q r).symm.trans hcount
      have hcenters' := hc.followsCenters P P' q r _ hcenters
      rw [A.surfaceIncidenceCenters_comap_etale ℓ hb hd hlevel D AM q (q ≫ f) (J.comap q)
        B hbB hdB (fun l => (D l).comap q) BM rfl rfl (fun _ => rfl)] at hcenters'
      have hP' := hc.uniformBoundaryCompatible P P' q r β D hP
      have hboundary := hc.boundaryAtLength P P' q r β D (fun l => (D l).comap q)
        (fun _ => rfl) (Fintype.card (Finset β)) hcount hcount'
      obtain ⟨W, k', M', Q', s, hQ', hcomp⟩ := ih V' (P'.endpoint_dimension_le 2 hdV) h' L'
        (P'.boundaryAtLength (fun l => (D l).comap q) _ hcount') r hrstructure hK
        (fun l => congrFun hboundary l)
      exact ⟨W, k', M', P'.append Q', s,
        .refine B hbB hdB hlevel BM P' hcenters' hcount' hP' Q' hQ',
        hc.append P P' q r Q Q' s hcomp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
