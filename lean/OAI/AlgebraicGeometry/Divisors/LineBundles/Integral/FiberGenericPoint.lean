import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Fiber Generic Point -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual fiber generic points for morphisms with geometrically integral fibers -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [GeometricallyIntegral f]

def integralFiberGenericPoint (y : Y) : X :=
  f.fiberι y (genericPoint (f.fiber y))

theorem integralFiberGenericPoint_projection (y : Y) : f (integralFiberGenericPoint f y) = y :=
  (f.range_fiberι y).le ⟨genericPoint (f.fiber y), rfl⟩

theorem integralFiberGenericPoint_specializes (y : Y) (x : X) (hx : f x = y) :
    integralFiberGenericPoint f y ⤳ x := by
  obtain ⟨z, rfl⟩ := (f.range_fiberι y).ge hx
  exact (genericPoint_specializes z).map (f.fiberι y).continuous

theorem integralFiberGenericPoint_injective : Function.Injective (integralFiberGenericPoint f) :=
  Function.LeftInverse.injective (integralFiberGenericPoint_projection f)

theorem integralFiberGenericPoint_unique (y : Y) (x : X) (hx : f x = y)
    (hgeneric : ∀ z, f z = y → x ⤳ z) : x = integralFiberGenericPoint f y :=
  ((hgeneric _ (integralFiberGenericPoint_projection f y)).antisymm
    (integralFiberGenericPoint_specializes f y x hx)).eq

def integralFiberCycleExtension : (Y →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (integralFiberGenericPoint f)

theorem integralFiberCycleExtension_injective : Function.Injective (integralFiberCycleExtension f) := by
  exact Finsupp.mapDomain_injective (integralFiberGenericPoint_injective f)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Integral.FiberGenericPoint.BundleCycles
