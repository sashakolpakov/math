import OAI.AlgebraicGeometry.Resolution.Blowups.Uniform.IncidenceSurfaceProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonBoundary

/-! # Incidence Surface Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Uniform

noncomputable section

/-! Complete prescribed-level surface incidence programs compare at every actual blowup step under étale restriction. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram.exists_etaleComparison
    {n m : ℕ} {β : Type} [Fintype β] {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K}
    (T : IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β X f J D Y g K P) :
    ∀ {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {L : V.IdealSheafData} {M : W.IdealSheafData} {E : β → V.IdealSheafData}
      {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V h L W k M},
      IncidenceSurfaceProgram.Construction.UniformIncidenceSurfaceProgram n m β V h L E W k M Q →
      ∀ (q : V ⟶ X) [Etale q], q ≫ f = h → J.comap q = L → (∀ l, (D l).comap q = E l) →
      ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  induction T with
  | terminal hstop A ht =>
      intro V W h k L M E Q S q hq hstructure hJ hD
      cases S with
      | terminal => exact ⟨q, hq, hstructure, hJ, rfl⟩
      | refine B hb hd hlevel BM R hcenters hcount hR U rest => omega
  | @refine ℓ β hβ X hX hNX hcompact f J D A ha hdA hlevel AM Y Z g h K L P hcenters hcount hP Q tail ih =>
      intro V W v w M N E S U q hq hstructure hJ hD
      cases U with
      | terminal hstop => omega
      | @refine _ _ _ V hV hNV hcompactV v M E B hb hdB hlevelB BM V' W v' w M' N R hRcenters hRcount hR S rest =>
          have hlist := A.surfaceIncidenceCenters_comap_etale ℓ ha hdA hlevel D AM q v M B hb hdB E BM
            hstructure hJ hD
          have hRcenters' : R.followsCenters
              ((A.surfaceIncidenceCenters ℓ ha hdA hlevel D).map (fun C => C.comap q)) := by
            rw [hlist]
            exact hRcenters
          obtain ⟨r, hr⟩ := P.exists_etaleComparison_of_followsCenters _ hcenters R q hstructure hJ hRcenters'
          obtain ⟨het, hpb, hK⟩ := hr.endpoint_pullback P R q r
          let : Etale r := het
          have hboundary := hr.boundaryAtLength P R q r β D E hD _ hcount hRcount
          have hover : r ≫ g = v' := by
            rw [← P.over, ← Category.assoc, hpb.w, Category.assoc, hstructure, R.over]
          obtain ⟨s, hs⟩ := ih rest r hover hK (fun l => congrFun hboundary l)
          exact ⟨s, hr.append P R q r Q S s hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Uniform
