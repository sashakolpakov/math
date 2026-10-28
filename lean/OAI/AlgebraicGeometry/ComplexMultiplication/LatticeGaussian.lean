import Mathlib.Algebra.Module.ZLattice.Summable
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.DiscreteSubset

/-! # Lattice Gaussian -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM

noncomputable section

/-! Gaussian series on discrete lattices, including polynomial factors and
arbitrary linear terms in the exponent. These estimates supply locally
uniform bounds for theta sections and their derivatives. -/

open Filter _root_.Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] (L : Submodule ℤ V) [DiscreteTopology L]

/-- Only finitely many vectors of a discrete lattice have bounded norm. -/
theorem lattice_norm_tendsto_cofinite :
    Tendsto (fun l : L => ‖l‖) cofinite atTop := by
  have hs : IsClosed (L : Set V) := @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  change Tendsto (fun l : L => ‖(l : V)‖) cofinite atTop
  exact (tendsto_norm_cocompact_atTop : Tendsto (norm : V → ℝ) (cocompact V) atTop).comp
    (hs.tendsto_coe_cofinite_of_isDiscrete DiscreteTopology.isDiscrete)

/-- A quadratic Gaussian with any polynomial prefactor eventually beats every inverse power. -/
theorem gaussian_poly_eventually_le (a b : ℝ) (ha : 0 < a) (k n : ℕ) :
    ∀ᶠ x : ℝ in atTop,
      ‖x ^ k * Real.exp (-a * x ^ 2 + b * x)‖ ≤ x⁻¹ ^ n := by
  have hp := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (k + n)).eventually
    (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop ((b + 1) / a), hp]
    with x hx hxa hxp
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hax : b + 1 ≤ a * x := by
    simpa only [mul_comm] using (div_le_iff₀ ha).mp hxa
  have hex : -a * x ^ 2 + b * x ≤ -x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hax) hx0.le]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx0.le _) (Real.exp_pos _).le),
    inv_pow, inv_eq_one_div, le_div_iff₀ (pow_pos hx0 n)]
  calc
    x ^ k * Real.exp (-a * x ^ 2 + b * x) * x ^ n ≤
        x ^ k * Real.exp (-x) * x ^ n := by gcongr
    _ = x ^ (k + n) * Real.exp (-x) := by rw [pow_add]; ring
    _ ≤ 1 := hxp.le

/-- Gaussian decay is summable on the actual lattice in its ambient norm. -/
theorem lattice_gaussian_poly_summable (a b : ℝ) (ha : 0 < a) (k : ℕ) :
    Summable (fun l : L => ‖l‖ ^ k * Real.exp (-a * ‖l‖ ^ 2 + b * ‖l‖)) := by
  let n := Module.finrank ℤ L + 1
  apply (ZLattice.summable_norm_pow_inv L n (by dsimp [n]; omega)).of_norm_bounded_eventually
  exact (lattice_norm_tendsto_cofinite L).eventually (gaussian_poly_eventually_le a b ha k n)

theorem lattice_gaussian_summable (a b : ℝ) (ha : 0 < a) :
    Summable (fun l : L => Real.exp (-a * ‖l‖ ^ 2 + b * ‖l‖)) := by
  simpa only [pow_zero, one_mul] using lattice_gaussian_poly_summable L a b ha 0

end

end OAI.AlgebraicGeometry.ComplexMultiplication.LatticeGaussian.CM
