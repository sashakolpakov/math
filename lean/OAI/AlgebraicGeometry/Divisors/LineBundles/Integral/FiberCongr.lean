import OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint

/-! # Fiber Congr -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberCongr.BundleCycles

noncomputable section

/-! Fiber generic points and their cycle extension depend only on the
actual scheme morphism, not on its presentation or property proof. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory

theorem integralFiberGenericPoint_congr {E X : Scheme.{0}} (p q : E ⟶ X)
    [GeometricallyIntegral p] [GeometricallyIntegral q] (h : p = q) (x : X) :
    FiberGenericPoint.BundleCycles.integralFiberGenericPoint p x = FiberGenericPoint.BundleCycles.integralFiberGenericPoint q x := by
  subst q
  rfl

theorem integralFiberCycleExtension_congr {E X : Scheme.{0}} (p q : E ⟶ X)
    [GeometricallyIntegral p] [GeometricallyIntegral q] (h : p = q) :
    FiberGenericPoint.BundleCycles.integralFiberCycleExtension p = FiberGenericPoint.BundleCycles.integralFiberCycleExtension q := by
  subst q
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberCongr.BundleCycles
