import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.Truncation

/-! # Envelope Factor -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeFactor.PDEnvelopeFactor

noncomputable section

/-!
# Cohomology: factoring the envelope through nilpotent truncations

Evaluation in a target whose divided-power ideal is nilpotent factors
uniquely through a sufficiently high truncation of the envelope.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (I₀ : Ideal R) (δ₀ : DividedPowers I₀) (I : Ideal A)
variable (T : EnvelopeDp.PDEnvelope.Target R A I₀ δ₀ I)

local notation "E" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.Envelope R A I₀ δ₀ I
local notation "J" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.ideal R A I₀ δ₀ I
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeDp.PDEnvelope.dividedPowers R A I₀ δ₀ I

/-- A nilpotence bound in the target kills the corresponding power in the envelope. -/
theorem power_le_kernel (n : ℕ) (hn : T.ideal ^ (n + 1) = 0) :
    J ^ (n + 1) ≤ RingHom.ker (EnvelopeDp.PDEnvelope.evaluate R A I₀ δ₀ I T) := by
  apply (Ideal.map_eq_bot_iff_le_ker _).mp
  apply le_antisymm _ bot_le
  rw [Ideal.map_pow]
  have h := pow_le_pow_left'
    (EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R A I₀ δ₀ I T).ideal_comp (n + 1)
  exact h.trans (by rw [hn]; rfl)

/-- The descended evaluation map. -/
def liftThrough (n : ℕ) (hn : T.ideal ^ (n + 1) = 0) : Truncation.PDTruncation.Ring E J n →ₐ[A] T.ring :=
  Ideal.Quotient.liftₐ (J ^ (n + 1)) (EnvelopeDp.PDEnvelope.lift R A I₀ δ₀ I T)
    (power_le_kernel R A I₀ δ₀ I T n hn)

@[simp]
theorem liftThrough_mk (n : ℕ) (hn : T.ideal ^ (n + 1) = 0) (a : E) :
    liftThrough R A I₀ δ₀ I T n hn (Ideal.Quotient.mk (J ^ (n + 1)) a) =
      EnvelopeDp.PDEnvelope.evaluate R A I₀ δ₀ I T a := rfl

/-- The descended map still preserves divided powers. -/
theorem liftThrough_isDPMorphism (n : ℕ) (hn : T.ideal ^ (n + 1) = 0) :
    DividedPowers.IsDPMorphism (Truncation.PDTruncation.dividedPowers E J δ n) T.dp
      (liftThrough R A I₀ δ₀ I T n hn).toRingHom where
  ideal_comp := by
    change ((J).map (Ideal.Quotient.mk (J ^ (n + 1)))).map _ ≤ T.ideal
    rw [Ideal.map_map]
    exact (EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R A I₀ δ₀ I T).ideal_comp
  dpow_comp x hx := by
    obtain ⟨a, ha, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk (J ^ (n + 1)))
        Ideal.Quotient.mk_surjective).mp hx
    rw [show (Truncation.PDTruncation.dividedPowers E J δ n).dpow _ (Ideal.Quotient.mk (J ^ (n + 1)) a) =
        Ideal.Quotient.mk (J ^ (n + 1)) ((δ).dpow _ a) from
          DividedPowers.Quotient.dpow_apply δ (Truncation.PDTruncation.power_inf_isSubDPIdeal E J δ n) ha]
    exact (EnvelopeDp.PDEnvelope.evaluate_isDPMorphism R A I₀ δ₀ I T).dpow_comp a ha

/-- Uniqueness follows from the proved universal property of the envelope. -/
theorem liftThrough_unique (n : ℕ) (hn : T.ideal ^ (n + 1) = 0)
    (g : Truncation.PDTruncation.Ring E J n →ₐ[A] T.ring)
    (hg : DividedPowers.IsDPMorphism (Truncation.PDTruncation.dividedPowers E J δ n) T.dp g.toRingHom) :
    g = liftThrough R A I₀ δ₀ I T n hn := by
  have h := EnvelopeDp.PDEnvelope.lift_unique R A I₀ δ₀ I T
    (g.comp (Ideal.Quotient.mkₐ A (J ^ (n + 1))))
    (hg.comp _ (Truncation.PDTruncation.quotient_isDPMorphism E J δ n))
  apply AlgHom.ext
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun h a

/-- Every nilpotent divided-power target is reached from a finite truncation. -/
theorem exists_truncated_lift (hT : IsNilpotent T.ideal) :
    ∃ n : ℕ, ∃! g : Truncation.PDTruncation.Ring E J n →ₐ[A] T.ring,
      DividedPowers.IsDPMorphism (Truncation.PDTruncation.dividedPowers E J δ n) T.dp g.toRingHom := by
  obtain ⟨n, hn⟩ := hT
  have hn' : T.ideal ^ (n + 1) = 0 := by rw [pow_succ, hn, zero_mul]
  exact ⟨n, liftThrough R A I₀ δ₀ I T n hn', liftThrough_isDPMorphism R A I₀ δ₀ I T n hn',
    fun g hg => liftThrough_unique R A I₀ δ₀ I T n hn' g hg⟩

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.EnvelopeFactor.PDEnvelopeFactor
