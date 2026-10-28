import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.LogarithmicProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceNaturality

/-! # Logarithmic Program Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Component initialization and every subsequent incidence step commute with étale restriction at a common coefficient level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem LogarithmicProgram.Construction.SurfaceLogarithmicProgram.exists_etaleComparison
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : LogarithmicProgram.Construction.SurfaceLogarithmicProgram n m β X f J D Y g K P)
    {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} {E : β → V.IdealSheafData}
    {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M}
    (S : LogarithmicProgram.Construction.SurfaceLogarithmicProgram n m β V h L E W k M Q)
    (q : V ⟶ X) [Etale q] (hstructure : q ≫ f = h) (hJ : J.comap q = L)
    (hD : ∀ l, (D l).comap q = E l) : ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  cases T with
  | component A AM P hcenters hcount hP Q tail =>
      cases S with
      | component B BM R hRcenters hRcount hR S rest =>
          have hlist := A.componentIncidenceCenters_comap_etale D AM q _ _ B E BM hstructure hJ hD
          have hRcenters' : R.followsCenters ((A.componentIncidenceCenters D).map (fun C => C.comap q)) := by
            rw [hlist]
            exact hRcenters
          obtain ⟨r, hr⟩ := P.exists_etaleComparison_of_followsCenters _ hcenters R q hstructure hJ hRcenters'
          obtain ⟨het, hpb, hK⟩ := hr.endpoint_pullback P R q r
          let : Etale r := het
          have hboundary := hr.boundaryAtLength P R q r β D E hD _ hcount hRcount
          have hover := congrArg (fun u => u ≫ f) hpb.w
          simp only [Category.assoc, P.over, hstructure, R.over] at hover
          obtain ⟨s, hs⟩ := tail.exists_etaleComparison rest r hover hK (fun l => congrFun hboundary l)
          exact ⟨s, hr.append P R q r Q S s hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
