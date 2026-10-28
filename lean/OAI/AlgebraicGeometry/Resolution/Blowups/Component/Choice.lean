import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.Coordinate.Regularity

/-! # Choice -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component

noncomputable section

/-! Every component-center choice defines a smooth center with an isomorphic ambient blowup. -/

open _root_.CategoryTheory

universe u

variable {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {R : Type u} [CommRing R] [Algebra k R] [Algebra ℚ R] [Algebra.Smooth k R]
    {J : Ideal R} {n : ℕ}

omit [Algebra ℚ R] in
theorem CenterChoice.Construction.ComponentCenterChoice.center_smooth (C : CenterChoice.Construction.ComponentCenterChoice k R J n) : Algebra.Smooth k (R ⧸ C.center) := by
  cases C with
  | terminal _ =>
      have h := DifferentialSaturationComponents.Construction.relativeDifferentialSaturation_quotient_smooth k (⊤ : Ideal R)
      rw [DifferentialSaturation.Construction.relativeDifferentialSaturation_top] at h
      exact h
  | normal z D hD _ =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      exact Coefficient.Component.Construction.coefficientComponentCenter_smooth k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)

theorem CenterChoice.Construction.ComponentCenterChoice.blowup_isIso (C : CenterChoice.Construction.ComponentCenterChoice k R J n) : IsIso (ReesGrading.Construction.affineBlowupToSpec C.center) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  cases C with
  | terminal _ =>
      exact PrincipalBlowup.Construction.affineBlowupToSpec_isIso_of_principal (⊤ : Ideal R) ⟨1, trivial⟩
        Ideal.span_singleton_one.symm isRegular_one
  | normal z D hD _ =>
      let : Algebra.Smooth k (R ⧸ Ideal.span {z}) := Blowups.Smooth.DifferentialHypersurface.Construction.smooth_quotient_of_derivation_one D z hD
      exact Coefficient.Component.Construction.coefficientComponentCenter_blowup_isIso k z (Coordinate.Regularity.Construction.coordinate_isRegular D z hD)
        (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)

omit [Algebra ℚ R] [Algebra.Smooth k R] [CharZero k] [IsAlgClosed k] in
theorem CenterChoice.Construction.ComponentCenterChoice.center_ne_bot [Nontrivial R] (C : CenterChoice.Construction.ComponentCenterChoice k R J n) : C.center ≠ ⊥ := by
  cases C with
  | terminal _ => exact top_ne_bot
  | normal z D hD hzT =>
      intro h
      have hz := Coefficient.ComponentNaturality.Construction.coefficientComponentCenter_normal_mem k z (Relative.DifferentialEquiv.Construction.relativeHomogenizedIdeal k J n) (n + 1)
      change z ∈ CenterChoice.Construction.ComponentCenterChoice.center (CenterChoice.Construction.ComponentCenterChoice.normal z D hD hzT) at hz
      rw [h, Ideal.mem_bot] at hz
      have hbad : (0 : R) = 1 := by simpa only [hz, map_zero] using hD
      exact zero_ne_one hbad

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component
