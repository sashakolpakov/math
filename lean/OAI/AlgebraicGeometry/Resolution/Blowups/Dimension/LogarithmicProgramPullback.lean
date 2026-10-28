import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.CoefficientNamedPullback
import OAI.AlgebraicGeometry.Resolution.Blowups.Dimension.LogarithmicProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.SurfaceProgramEtalePullback

/-! # Logarithmic Program Pullback -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Dimension

noncomputable section

/-! Full logarithmic programs pull back étale while retaining canonical component clearing and the coefficient schedule. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem LogarithmicProgram.Construction.DimensionLogarithmicProgram.exists_etale_pullback
    {d : ℕ} {𝒮 : Uniform.ControlProgramSystem.Construction.UniformControlProgramSystem d} {n : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {schedule : LogarithmicProgram.Construction.DimensionLogarithmicSchedule 𝒮 n β} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (H : LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 schedule X f J D Y g K P)
    (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V] [CompactSpace V]
    (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (E : β → V.IdealSheafData)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hL : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) :
    ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
      (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M) (r : W ⟶ Y),
      LogarithmicProgram.Construction.DimensionLogarithmicProgram 𝒮 schedule V h L E W k M Q ∧ P.EtaleComparison Q q r := by
  subst h
  subst L
  have he : (fun l => (D l).comap q) = E := funext hD
  subst E
  cases H with
  | component A AM P hcenters hcount hP Q tail =>
      have hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (q ≫ f) (J.comap q) (n + 1) = ⊤ := by
        rw [← Blowups.Smooth.GlobalCoefficientEtalePullback.Construction.smoothDifferentialIdealSheaf_comap_etale, A.ordinary_bound, Scheme.IdealSheafData.comap_top]
      obtain ⟨B⟩ := GlobalComponent.ChoiceAtlas.Construction.exists_global_component_choice_atlas (q ≫ f) (J.comap q) n hbound
      have hcenter := A.center_comap_etale q B
      let BM : Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (q ≫ f) B.center (fun l => (D l).comap q) := by
        rw [← hcenter]
        exact AM.comapEtale f q
      obtain ⟨V', h', L', P', r, hc⟩ := P.exists_etale_pullback V (q ≫ f) (J.comap q) q rfl rfl
      let : Smooth _ := P.endpoint_smooth
      let : Smooth h' := P'.endpoint_smooth
      let : IsIntegral V' := P'.endpoint_integral
      let : IsLocallyNoetherian V' := LocallyOfFiniteType.isLocallyNoetherian h'
      let : CompactSpace V' := QuasiCompact.compactSpace_of_compactSpace P'.toBase
      obtain ⟨hr, _, hK⟩ := hc.endpoint_pullback P P' q r
      let : Etale r := hr
      have hrstructure := hc.endpoint_structure P P' q r
      have hcount' : P'.stepCount = Fintype.card (Finset β) := (hc.stepCount_eq P P' q r).symm.trans hcount
      have hcenters' := hc.followsCenters P P' q r _ hcenters
      rw [A.componentIncidenceCenters_comap_etale D AM q (q ≫ f) (J.comap q)
        B (fun l => (D l).comap q) BM rfl rfl (fun _ => rfl)] at hcenters'
      have hP' := hc.uniformBoundaryCompatible P P' q r β D hP
      have hboundary := hc.boundaryAtLength P P' q r β D (fun l => (D l).comap q)
        (fun _ => rfl) (Fintype.card (Finset β)) hcount hcount'
      obtain ⟨W, k', M', Q', s, hQ', hcomp⟩ := tail.exists_etale_pullback V' h' L'
        (P'.boundaryAtLength (fun l => (D l).comap q) _ hcount') r hrstructure hK
        (fun l => congrFun hboundary l)
      exact ⟨W, k', M', P'.append Q', s, .component B BM P' hcenters' hcount' hP' Q' hQ',
        hc.append P P' q r Q Q' s hcomp⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Dimension
