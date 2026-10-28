import OAI.AlgebraicGeometry.Resolution.Blowups.Component.CenterChoice
import OAI.AlgebraicGeometry.Resolution.Blowups.Coefficient.Bound
import OAI.AlgebraicGeometry.Resolution.Blowups.HomogenizationIdempotence

/-! # Center Monotonicity -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Component

noncomputable section

/-! Enlarging a marked ideal enlarges its intrinsic component center. -/

universe u

theorem CenterMonotonicity.Construction.relativeDifferentialSaturation_mono
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    {J L : Ideal R} (h : J ≤ L) : DifferentialSaturation.Construction.relativeDifferentialSaturation k J ≤ DifferentialSaturation.Construction.relativeDifferentialSaturation k L :=
  iSup_mono (fun m => Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k m h)

theorem CenterMonotonicity.Construction.coefficientComponentCenter_mono
    (k : Type u) {R : Type u} [CommRing k] [CommRing R] [Algebra k R]
    (z : R) (b : ℕ) {J L : Ideal R} (h : J ≤ L) :
    Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z J b ≤ Coefficient.ComponentNaturality.Construction.coefficientComponentCenter k z L b :=
  Ideal.comap_mono (CenterMonotonicity.Construction.relativeDifferentialSaturation_mono k (Coefficient.Bound.Construction.relativeCoefficientIdeal_mono k z b h))

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R] {J L : Ideal R} {n : ℕ}

def CenterChoice.Construction.ComponentCenterChoice.enlarge (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (h : J ≤ L) : CenterChoice.Construction.ComponentCenterChoice k R L n := by
  cases C with
  | terminal ht =>
      exact .terminal (top_le_iff.mp (ht ▸ Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n h))
  | normal z D hD hz => exact .normal z D hD (Relative.DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k n h hz)

theorem CenterChoice.Construction.ComponentCenterChoice.center_le_enlarge (C : CenterChoice.Construction.ComponentCenterChoice k R J n) (h : J ≤ L) :
    C.center ≤ (C.enlarge h).center := by
  cases C with
  | terminal _ => exact le_rfl
  | normal z D hD hz =>
      exact CenterMonotonicity.Construction.coefficientComponentCenter_mono k z (n + 1) (HomogenizationIdempotence.Construction.relativeHomogenizedIdeal_mono k h n)

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Component
