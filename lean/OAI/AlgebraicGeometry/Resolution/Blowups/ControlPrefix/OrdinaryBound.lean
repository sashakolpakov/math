import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.ControlPrefix
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderBoundPreservation

/-! # Ordinary Bound -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The ordinary differential bound persists along an actual prefix at its fixed control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.endpoint_differential_bound
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ [Smooth f], Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J b = ⊤ →
      letI : Smooth g := P.endpoint_smooth
      Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g K b = ⊤ := by
  induction P with
  | stop => intro _ h; exact h
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro hf h
      let : Smooth f := hf
      let : Smooth (I.subschemeι ≫ f) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      exact ih (Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound f I J hI b hp h)

end

end OAI.AlgebraicGeometry.Resolution.Blowups
