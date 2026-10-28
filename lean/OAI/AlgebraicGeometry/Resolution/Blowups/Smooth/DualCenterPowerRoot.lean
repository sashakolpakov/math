import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.FrameCenterPowerRoot
import OAI.AlgebraicGeometry.Resolution.Blowups.DualFrameCenterSmooth

/-! # Dual Center Power Root -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DualCenterPowerRoot.Construction

noncomputable section

/-! Exact ideal and coefficient powers for actual smooth dual-coordinate centers. -/

universe u

variable (k : Type u) {R ι : Type u} [Field k] [IsAlgClosed k] [CommRing R]
  [Algebra k R] [Algebra.Smooth k R] [Algebra ℚ R] [Fintype ι] [DecidableEq ι]

/-- Dual coordinate derivations themselves supply reducedness of the
center, so exact ideal power scaling needs no separate radicality hypothesis. -/
theorem smooth_dual_center_ideal_power_root (z : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (J : Ideal R)
    (b e : ℕ) (he : 0 < e) (hJ : J ^ e ≤ (Ideal.span (Set.range z)) ^ (b * e)) :
    J ≤ (Ideal.span (Set.range z)) ^ b :=
  FrameCenterPowerRoot.Construction.smooth_frame_center_ideal_power_root k z (fun i => (D i).restrictScalars ℤ)
    hD (DualFrameCenterSmooth.Construction.dual_derivation_family_center_isRadical z D hD) J b e he hJ

/-- Along a smooth dual-coordinate center in any dimension, the factorial
coefficient ideal encodes exactly the original component power bounds. -/
theorem smooth_dual_center_weighted_iff (z : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (z j) = if i = j then 1 else 0) (b : ℕ) (J : Fin b → Ideal R) :
    WeightedCoefficientIdeal.Construction.weightedCoefficientIdeal b J ≤ (Ideal.span (Set.range z)) ^ b.factorial ↔
      ∀ j, J j ≤ (Ideal.span (Set.range z)) ^ (b - j.val) :=
  FrameCenterPowerRoot.Construction.smooth_frame_center_weighted_iff k z (fun i => (D i).restrictScalars ℤ)
    hD (DualFrameCenterSmooth.Construction.dual_derivation_family_center_isRadical z D hD) b J

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.DualCenterPowerRoot.Construction
