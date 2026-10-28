import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.UniformIncidenceTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBoundaryCenterExtension
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.PrincipalBlowup
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonOpen

/-! # Terminal Incidence Trace Program -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.TerminalIncidenceTraceProgram.Construction

noncomputable section

/-! Terminal marked ideals realize any specified incidence trace using actual unit-center blowups. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem exists_terminal_program_with_incidence_trace
    (b : ℕ) (hb : 0 < b) {β : Type} (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β) :
    ∀ [Fintype β] (X : Scheme) [IsIntegral X] [IsLocallyNoetherian X]
      (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData)
      (D : β → X.IdealSheafData) (_A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]),
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1) = ⊤ →
      ∃ (Y : Scheme) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData)
        (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K),
        letI : Smooth g := P.endpoint_smooth
        P.HasIncidenceTrace β D T ∧ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K (b - 1) = ⊤ := by
  induction T with
  | stop β =>
      intro _ X _ _ f _ J D A ht
      exact ⟨X, f, J, .stop, ⟨A⟩, ht⟩
  | @step β F T ih =>
      intro _ X _ _ f _ J D A ht
      let hI : (⊤ : X.IdealSheafData) ≠ ⊥ := Integral.IdealSheafProducts.Construction.idealSheaf_top_ne_bot
      let B := A.unitCenter.withUniformIncidence F (fun _ hp => (hp rfl).elim)
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase ⊤ hI
      let : IsIso π := Global.PrincipalBlowup.Construction.globalBlowupToBase_isIso_of_locallyPrincipal ⊤ hI (Locally.PrincipalIdealSheaf.Construction.LocallyPrincipalIdealSheaf.top X)
      let : Smooth (π ≫ f) := inferInstance
      have hp : J ≤ (⊤ : X.IdealSheafData) ^ b := by
        rw [← Scheme.IdealSheafData.one_eq_top, one_pow]
        exact le_top
      have hnext : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (π ≫ f) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ J hI b) (b - 1) = ⊤ := by
        rw [Global.PrincipalBlowup.Construction.globalBlowupControlledIdeal_top_center, ← Blowups.Smooth.DifferentialSheafRestriction.Construction.smoothDifferentialIdealSheaf_comap_open,
          ht, Scheme.IdealSheafData.comap_top]
      obtain ⟨Y, g, K, P, hP, hterminal⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup ⊤ hI) (π ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal ⊤ J hI b) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary ⊤ hI D) (B.blowupBoundary hI) hnext
      exact ⟨Y, g, K, .blowup ⊤ hI hb hp B.center_smooth inferInstance P,
        ⟨⟨B, fun _ => rfl⟩, hP⟩, hterminal⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.TerminalIncidenceTraceProgram.Construction
