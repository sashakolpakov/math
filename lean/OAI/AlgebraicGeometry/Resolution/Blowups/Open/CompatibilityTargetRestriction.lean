import OAI.AlgebraicGeometry.Resolution.Blowups.Open.ComparisonAt

/-! # Compatibility Target Restriction -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual pointed compatibility restricts along a monomorphic common target map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.OpenCompatible.of_postcomp
    {b : ℕ} {X X' U V Y Z : Scheme} {f : U ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {I : U.IdealSheafData} {J : V.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    {P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b U f I Y h K} {Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V g J Z k L}
    (j : U ⟶ X') (l : V ⟶ X') (q : X' ⟶ X) [Mono q]
    (H : P.OpenCompatible Q (j ≫ q) (l ≫ q)) : P.OpenCompatible Q j l := by
  intro x y hxy
  obtain ⟨S, T, s, t, A, B, R, a, c, r, v, z, hx, hy, he, ha, hc⟩ := H x y (congrArg q hxy)
  refine ⟨S, T, s, t, A, B, R, a, c, r, v, z, hx, hy, ?_, ha, hc⟩
  apply (cancel_mono q).mp
  simpa only [Category.assoc] using he

end

end OAI.AlgebraicGeometry.Resolution.Blowups
