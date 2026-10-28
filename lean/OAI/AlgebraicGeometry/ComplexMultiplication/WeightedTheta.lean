import OAI.AlgebraicGeometry.ComplexMultiplication.SiegelThetaSeries
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! # Weighted Theta -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication

noncomputable section

/-!
# Theta series with bounded complex lattice inputs

The input is an actual bounded function on a discrete lattice. This includes
restrictions of finite Schwartz inputs, once their support lattice is supplied,
and allows arbitrary complex linear combinations. Gaussian estimates justify
the sums, differentiation, and linearity. No transformation law is assumed.
-/

open scoped Classical BoundedContinuousFunction
open Filter _root_.Topology _root_.Metric

def WeightedTheta.CM.thetaIndicatorInput {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (S : Set X) : X →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => if x ∈ S then 1 else 0)
    continuous_of_discreteTopology 1 (fun x => by split_ifs <;> simp)

theorem WeightedTheta.CM.thetaIndicatorInput_apply {X : Type*} [TopologicalSpace X] [DiscreteTopology X]
    (S : Set X) (x : X) : WeightedTheta.CM.thetaIndicatorInput S x = if x ∈ S then 1 else 0 := rfl

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℂ U]
  (Z : CMSiegelPhase.CM.SiegelPhase V) (P : V →L[ℝ] (U →L[ℂ] ℂ)) (L : Submodule ℤ V)

def CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm (φ : L →ᵇ ℂ) (x : L) (z : U) : ℂ :=
  φ x * Z.thetaTerm P x z

def CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative (φ : L →ᵇ ℂ) (x : L) (z : U) : U →L[ℂ] ℂ :=
  φ x • Z.thetaTermDerivative P x z

theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm_hasFDerivAt (φ : L →ᵇ ℂ) (x : L) (z : U) :
    HasFDerivAt (Z.weightedThetaTerm P L φ x)
      (Z.weightedThetaTermDerivative P L φ x z) z :=
  (Z.thetaTerm_hasFDerivAt P x z).const_smul (φ x)

def CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries (φ : L →ᵇ ℂ) (z : U) : ℂ :=
  ∑' x : L, Z.weightedThetaTerm P L φ x z

def CMSiegelPhase.CM.SiegelPhase.weightedThetaSeriesDerivative (φ : L →ᵇ ℂ) (z : U) : U →L[ℂ] ℂ :=
  ∑' x : L, Z.weightedThetaTermDerivative P L φ x z

variable [FiniteDimensional ℝ V] [DiscreteTopology L]

theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm_norm_summable (φ : L →ᵇ ℂ) (z : U) :
    Summable (fun x : L => ‖Z.weightedThetaTerm P L φ x z‖) := by
  apply ((Z.thetaTerm_norm_summable P L z).mul_left ‖φ‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro x
  rw [CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, norm_mul]
  exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm x) (norm_nonneg _)

omit [DiscreteTopology L] in
theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative_norm_le (φ : L →ᵇ ℂ) (R : ℝ)
    (x : L) (z : U) (hz : ‖z‖ ≤ R) :
    ‖Z.weightedThetaTermDerivative P L φ x z‖ ≤ ‖φ‖ * Z.thetaDerivativeMajorant P R x := by
  rw [CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative, norm_smul]
  exact mul_le_mul (φ.norm_coe_le_norm x) (Z.thetaTermDerivative_norm_le P R x z hz)
    (norm_nonneg _) (norm_nonneg _)

theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative_norm_summable (φ : L →ᵇ ℂ) (z : U) :
    Summable (fun x : L => ‖Z.weightedThetaTermDerivative P L φ x z‖) := by
  exact ((Z.thetaDerivativeMajorant_summable P L ‖z‖).mul_left ‖φ‖).of_nonneg_of_le
    (fun _ => norm_nonneg _)
    (fun x => Z.weightedThetaTermDerivative_norm_le P L φ ‖z‖ x z le_rfl)

theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries_hasFDerivAt (φ : L →ᵇ ℂ) (z : U) :
    HasFDerivAt (Z.weightedThetaSeries P L φ) (Z.weightedThetaSeriesDerivative P L φ z) z := by
  let R : ℝ := ‖z‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hz : z ∈ ball (0 : U) R := by
    simp only [mem_ball, dist_zero_right]
    dsimp [R]
    linarith
  exact hasFDerivAt_tsum_of_isPreconnected
    ((Z.thetaDerivativeMajorant_summable P L R).mul_left ‖φ‖) isOpen_ball
    (convex_ball (0 : U) R).isPreconnected
    (fun x w _ => Z.weightedThetaTerm_hasFDerivAt P L φ x w)
    (fun x w hw => Z.weightedThetaTermDerivative_norm_le P L φ R x w
      (show ‖w‖ < R by simpa only [mem_ball, dist_zero_right] using hw).le)
    (mem_ball_self hR) (Z.weightedThetaTerm_norm_summable P L φ 0).of_norm hz

theorem CMSiegelPhase.CM.SiegelPhase.fderiv_weightedThetaSeries (φ : L →ᵇ ℂ) (z : U) :
    fderiv ℂ (Z.weightedThetaSeries P L φ) z = Z.weightedThetaSeriesDerivative P L φ z :=
  (Z.weightedThetaSeries_hasFDerivAt P L φ z).fderiv

theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries_add (φ ψ : L →ᵇ ℂ) (z : U) :
    Z.weightedThetaSeries P L (φ + ψ) z =
      Z.weightedThetaSeries P L φ z + Z.weightedThetaSeries P L ψ z := by
  simp only [CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries, CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, BoundedContinuousFunction.add_apply, add_mul]
  exact ((Z.weightedThetaTerm_norm_summable P L φ z).of_norm).tsum_add
    (Z.weightedThetaTerm_norm_summable P L ψ z).of_norm

omit [FiniteDimensional ℝ V] [DiscreteTopology L] in
theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries_smul (c : ℂ) (φ : L →ᵇ ℂ) (z : U) :
    Z.weightedThetaSeries P L (c • φ) z = c * Z.weightedThetaSeries P L φ z := by
  simp only [CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries, CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, BoundedContinuousFunction.smul_apply,
    smul_eq_mul, mul_assoc, tsum_mul_left]

/-- The theta sum depends complex linearly on its actual input. -/
def CMSiegelPhase.CM.SiegelPhase.weightedThetaSeriesLinear : (L →ᵇ ℂ) →ₗ[ℂ] (U → ℂ) where
  toFun := Z.weightedThetaSeries P L
  map_add' φ ψ := funext (Z.weightedThetaSeries_add P L φ ψ)
  map_smul' c φ := funext (Z.weightedThetaSeries_smul P L c φ)

omit [FiniteDimensional ℝ V] in
theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaSeries_indicator (S : Set L) (z : U) :
    Z.weightedThetaSeries P L (WeightedTheta.CM.thetaIndicatorInput S) z = Z.thetaSeriesOn P L S z := by
  apply tsum_congr
  intro x
  simp only [CMSiegelPhase.CM.SiegelPhase.weightedThetaTerm, WeightedTheta.CM.thetaIndicatorInput_apply, CMSiegelPhase.CM.SiegelPhase.thetaTermOn]
  split_ifs <;> simp

omit [FiniteDimensional ℝ V] in
theorem CMSiegelPhase.CM.SiegelPhase.weightedThetaSeriesDerivative_indicator (S : Set L) (z : U) :
    Z.weightedThetaSeriesDerivative P L (WeightedTheta.CM.thetaIndicatorInput S) z =
      Z.thetaSeriesOnDerivative P L S z := by
  apply tsum_congr
  intro x
  by_cases hx : x ∈ S
  · simp [CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative, WeightedTheta.CM.thetaIndicatorInput_apply, CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative, hx]
  · simp only [CMSiegelPhase.CM.SiegelPhase.weightedThetaTermDerivative, WeightedTheta.CM.thetaIndicatorInput_apply, CMSiegelPhase.CM.SiegelPhase.thetaTermOnDerivative,
      ite_eq_right hx]
    ext u
    simp

end

end OAI.AlgebraicGeometry.ComplexMultiplication
