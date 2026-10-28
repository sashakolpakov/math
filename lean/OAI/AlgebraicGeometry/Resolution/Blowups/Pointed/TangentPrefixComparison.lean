import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.ComparisonHeads
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.TangentBlowupCongruence

/-! # Tangent Prefix Comparison -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Pointed common actual prefixes compare two choices on every point of the original order support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Smooth.ControlPrefix.Construction.SmoothControlPrefix.PointedTangentComparison
    {n : ℕ} {X Y Z : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {h : Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} {L : Z.IdealSheafData}
    (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Y g K) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) X f J Z h L) : Prop :=
  ∀ x : X, x ∈ (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n).support →
    ∃ (V W : Scheme) (v : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (w : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)
      (B : V.IdealSheafData) (C : W.IdealSheafData) (T : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix (n + 1) V v B W w C)
      (a b : V ⟶ X) (r : W ⟶ Y) (s : W ⟶ Z) (y : V), a y = x ∧
        IdealSheaf.CongruentMaps.Construction.IdealSheafCongruent a b (Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J n) ∧
        P.EtaleComparison T a r ∧ Q.EtaleComparison T b s

end

end OAI.AlgebraicGeometry.Resolution.Blowups
