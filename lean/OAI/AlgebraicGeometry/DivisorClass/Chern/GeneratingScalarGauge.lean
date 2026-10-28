import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.FieldSimp

/-! # Generating Scalar Gauge -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingScalarGauge

/-! The exact scalar identity for the original algebraic and holomorphic frame conventions. -/

theorem generatingChern_scalar_gauge (t u v c d a : ℂ)
    (ht : t ≠ 0) (hu : u ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : a * d / c = v / u) :
    a = t⁻¹ * ((t * v) / d) / (u / c) := by
  calc
    a = (v / u) * c / d := (eq_div_iff hd).mpr ((div_eq_iff hc).mp h)
    _ = t⁻¹ * ((t * v) / d) / (u / c) := by
      field_simp

end OAI.AlgebraicGeometry.DivisorClass.Chern.GeneratingScalarGauge
