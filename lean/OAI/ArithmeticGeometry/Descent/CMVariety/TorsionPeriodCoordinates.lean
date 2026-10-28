import OAI.ArithmeticGeometry.Descent.CMVariety.LogarithmicTorsionRigidity
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-! # Torsion Period Coordinates -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.TorsionPeriodCoordinates.Abelian

noncomputable section

/-!
Positive-order torsion points of a surjective exponential have exact
integer-period coordinates divided by their order. The coordinates use
the full actual kernel lattice and its compatible real frame.
-/

open scoped BigOperators Classical

variable {Index V : Type} [Fintype Index]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem realFrame_eq_sum (r : (Index → ℝ) →ₗ[ℝ] V) (v : Index → ℝ) :
    r v = ∑ i, v i • r (Pi.single i 1) := by
  classical
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact r.map_smul (v i) (Pi.single i 1)

theorem realFrame_integer_mem (Λ : Submodule ℤ V)
    (r : (Index → ℝ) →ₗ[ℝ] V)
    (hr : ∀ i, r (Pi.single i 1) ∈ Λ) (z : Index → ℤ) :
    r (fun i => (z i : ℝ)) ∈ Λ := by
  rw [realFrame_eq_sum]
  apply Submodule.sum_mem
  intro i _
  rw [Int.cast_smul_eq_zsmul]
  exact Λ.smul_mem (z i) (hr i)

theorem realFrame_basis_repr (Λ : Submodule ℤ V)
    (b : Module.Basis Index ℤ Λ) (r : (Index → ℝ) →ₗ[ℝ] V)
    (hr : ∀ i, (b i : V) = r (Pi.single i 1)) (l : Λ) :
    r (fun i => (b.repr l i : ℝ)) = (l : V) := by
  rw [realFrame_eq_sum]
  have h := congrArg (fun a : Λ => (a : V)) (b.sum_repr l)
  simpa only [← hr, Submodule.coe_sum, Submodule.coe_smul, Int.cast_smul_eq_zsmul] using h

theorem torsion_of_integer_period_coordinates
    {G : Type} [Group G] (exponential : V → G)
    (hzero : exponential 0 = 1)
    (hadd : ∀ v w, exponential (v + w) = exponential v * exponential w)
    (Λ : Submodule ℤ V) (hΛ : ∀ v, v ∈ Λ ↔ exponential v = 1)
    (r : (Index → ℝ) →ₗ[ℝ] V) (hr : ∀ i, r (Pi.single i 1) ∈ Λ)
    (n : ℕ) (hn : 0 < n) (z : Index → ℤ) :
    exponential ((n : ℝ)⁻¹ • r (fun i => (z i : ℝ))) ^ n = 1 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [← LogarithmicTorsionRigidity.Abelian.additive_exponential_nsmul exponential hzero hadd,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hn', one_smul]
  exact (hΛ _).mp (realFrame_integer_mem Λ r hr z)

theorem exists_integer_period_coordinates_of_torsion
    {G : Type} [Group G] (exponential : V → G)
    (hzero : exponential 0 = 1)
    (hadd : ∀ v w, exponential (v + w) = exponential v * exponential w)
    (hsurj : Function.Surjective exponential)
    (Λ : Submodule ℤ V) (hΛ : ∀ v, v ∈ Λ ↔ exponential v = 1)
    (b : Module.Basis Index ℤ Λ) (r : (Index → ℝ) →ₗ[ℝ] V)
    (hr : ∀ i, (b i : V) = r (Pi.single i 1))
    (n : ℕ) (hn : 0 < n) (x : G) (hx : x ^ n = 1) :
    ∃ z : Index → ℤ, exponential ((n : ℝ)⁻¹ • r (fun i => (z i : ℝ))) = x := by
  obtain ⟨v, hv⟩ := hsurj x
  have hl : (n : ℝ) • v ∈ Λ := by
    apply (hΛ _).mpr
    rw [Nat.cast_smul_eq_nsmul ℝ, LogarithmicTorsionRigidity.Abelian.additive_exponential_nsmul exponential hzero hadd, hv, hx]
  let l : Λ := ⟨(n : ℝ) • v, hl⟩
  refine ⟨fun i => b.repr l i, ?_⟩
  rw [realFrame_basis_repr Λ b r hr l]
  change exponential ((n : ℝ)⁻¹ • ((n : ℝ) • v)) = x
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  rw [smul_smul, inv_mul_cancel₀ hn', one_smul, hv]

end

end OAI.ArithmeticGeometry.Descent.CMVariety.TorsionPeriodCoordinates.Abelian
