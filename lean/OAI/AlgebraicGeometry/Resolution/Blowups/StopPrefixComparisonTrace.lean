import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.IncidenceTrace
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Stop Prefix Comparison Trace -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A comparison from a stopped prefix identifies the initial boundary data and has no blowup trace. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.trace_on_source_of_comparison_from_stop
    {b : ℕ} {X V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (q : V ⟶ X) (r : W ⟶ X)
    (hc : (.stop : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J X f J).EtaleComparison Q q r)
    (β : Type) [Fintype β] (D : β → X.IdealSheafData) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (hT : Q.HasIncidenceTrace β (fun l => (D l).comap q) T) :
    match T with
    | .stop _ => Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas (q ≫ f) (fun l => (D l).comap q) [Finset.univ])
    | .step _ _ => False := by
  cases Q with
  | stop =>
      obtain ⟨_, he, _, _⟩ := hc
      cases T with
      | stop => rw [he]; exact hT
      | step => exact hT
  | blowup => exact False.elim hc

end

end OAI.AlgebraicGeometry.Resolution.Blowups
