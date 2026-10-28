import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.TangentCenterChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.Component.Choice

/-! # Tangent Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Geometry of the finite-order surface coefficient center. -/

universe u

theorem TangentCenterChoice.Construction.SurfaceTangentCenterChoice.center_smooth {k R : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    {J : Ideal R} {n ℓ : ℕ} (C : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ)
    (hdim : ringKrullDim R ≤ 2) (hlevel : (n + 1).factorial ≤ ℓ + 1) :
    Algebra.Smooth k (R ⧸ C.center) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  cases C with
  | terminal ht => exact (Component.CenterChoice.Construction.ComponentCenterChoice.terminal ht).center_smooth
  | normal z D hD _ hb =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      have hd := NormalQuotientDimension.Construction.normal_quotient_dimension_induction D z hD 1 hdim
      exact (Coefficient.TangentCurveCenter.Construction.coefficientTangentCenter_curve_permissible k D z hD
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ hd hlevel hb).2

theorem TangentCenterChoice.Construction.SurfaceTangentCenterChoice.center_ne_bot {k R : Type u} [CommRing k] [CommRing R] [Nontrivial R] [Algebra k R]
    {J : Ideal R} {n ℓ : ℕ} (C : TangentCenterChoice.Construction.SurfaceTangentCenterChoice k R J n ℓ) : C.center ≠ ⊥ := by
  cases C with
  | terminal _ => exact top_ne_bot
  | normal z D hD hz hb =>
      intro h
      have hm := Coefficient.TangentNaturality.Construction.coefficientTangentCenter_normal_mem k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1) ℓ
      change z ∈ TangentCenterChoice.Construction.SurfaceTangentCenterChoice.center (TangentCenterChoice.Construction.SurfaceTangentCenterChoice.normal z D hD hz hb) at hm
      rw [h, Ideal.mem_bot] at hm
      have hbad : (0 : R) = 1 := by simpa only [hm, map_zero] using hD
      exact zero_ne_one hbad

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
