import OAI.AlgebraicGeometry.Foundations.Scheme.SmoothProjectiveDecomposition
import Mathlib.AlgebraicGeometry.Fiber

/-! # Fiber Reduced -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.FiberReduced.BundleCycles

noncomputable section

/-! The actual scheme-theoretic fibers of a smooth morphism are reduced. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

theorem smoothFiber_isReduced {E X : Scheme.{0}} (p : E ⟶ X) [Smooth p] (x : X) :
    IsReduced (p.fiber x) := by
  let hs : Smooth (p.fiberToSpecResidueField x) :=
    inferInstanceAs (Smooth (pullback.snd p (X.fromSpecResidueField x)))
  exact @Foundations.Scheme.SmoothProjectiveDecomposition.smoothScheme_isReduced (X.residueField x) inferInstance (p.fiber x)
    (p.fiberToSpecResidueField x) hs

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Smooth.FiberReduced.BundleCycles
