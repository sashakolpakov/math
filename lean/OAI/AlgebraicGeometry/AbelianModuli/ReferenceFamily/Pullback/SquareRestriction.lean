import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.TensorCechCoefficients
import OAI.RepresentationTheory.Theta.Geometric.Pullback.SquareFrames

/-! # Square Restriction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareRestriction

noncomputable section

/-! Actual square-pulled frames commute with restriction to any
smaller commuting open square. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem pullbackSquareFrame_restrict {X Y : Scheme.{0}} (f : X ⟶ Y) (M : Y.Modules)
    {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U) (hV : V' ≤ V)
    (p : V.toScheme ⟶ U.toScheme) (q : V'.toScheme ⟶ U'.toScheme)
    (hp : p ≫ U.ι = V.ι ≫ f) (hq : q ≫ U'.ι = V'.ι ≫ f)
    (hcomm : q ≫ Y.homOfLE hU = X.homOfLE hV ≫ p)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ ArithmeticGeometry.OrdinaryLocus.Openness.LineBundle.Construction.structureSheafModule U.toScheme) :
    Dual.TensorCechCoefficients.restrictPullbackFrame ((Scheme.Modules.pullback f).obj M) hV (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V.ι U.ι p hp M e) =
      RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V'.ι U'.ι q hq M (Dual.TensorCechCoefficients.restrictPullbackFrame M hU e) := by
  have h₁ := Dual.TensorCechCoefficients.restrictPullbackFrame_factored ((Scheme.Modules.pullback f).obj M) hV
    (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V.ι U.ι p hp M e)
  have h₂ := RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame_nested f V.ι V'.ι U.ι U'.ι (X.homOfLE hV) (Y.homOfLE hU) p q
    (X.homOfLE_ι hV) (Y.homOfLE_ι hU) hp hq hcomm M e
  have h₃ := congrArg (RepresentationTheory.Theta.Geometric.Pullback.SquareFrames.pullbackSquareFrame f V'.ι U'.ι q hq M) (Dual.TensorCechCoefficients.restrictPullbackFrame_factored M hU e).symm
  exact h₁.trans (h₂.trans h₃)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.SquareRestriction
