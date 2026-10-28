import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.HomogenizedTransport

/-! # Same Symmetry -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Sharing the same actual blowups is symmetric in the two marked controls. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups.symm {b c : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J L : X.IdealSheafData} {K M : Y.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K} {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix c X f L Y g M}
    (h : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups b c P Q) : Smooth.ControlPrefix.Construction.SmoothControlPrefix.SameBlowups c b Q P := by
  induction h with
  | stop => exact .stop
  | blowup I hI hb hc hp hq hs hbl tail ih => exact .blowup I hI hc hb hq hp hs hbl ih

end

end OAI.AlgebraicGeometry.Resolution.Blowups
