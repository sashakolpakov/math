import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison

/-! # Initial Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Complete actual prefix comparisons retain their initial structure map and marked ideal identities. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.EtaleComparison.initial_data
    {b : ℕ} {X Y V W : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : V.IdealSheafData} {M : W.IdealSheafData}
    (P : Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) (Q : Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M)
    (q : V ⟶ X) (r : W ⟶ Y) (H : P.EtaleComparison Q q r) :
    Etale q ∧ q ≫ f = h ∧ J.comap q = L := by
  cases P <;> cases Q
  · exact ⟨H.1, H.2.1, H.2.2.1⟩
  · exact False.elim H
  · exact False.elim H
  · exact ⟨H.1, H.2.1, H.2.2.1⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
