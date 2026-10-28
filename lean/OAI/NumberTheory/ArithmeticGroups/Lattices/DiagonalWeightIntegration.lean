import OAI.NumberTheory.ArithmeticGroups.Lattices.IntegerWeightComponents
import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Trace

/-! # Diagonal Weight Integration -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalWeightIntegration.Construction

noncomputable section

section

/-! Field-uniform diagonal special-linear homomorphisms associated to
integer weights with zero sum, with regular coordinates in (t,t⁻¹). -/

open scoped Classical
open _root_.Matrix _root_.MvPolynomial

theorem prod_unit_zpow_sum {K I : Type*} [Field K] (t : Kˣ) (w : I → ℤ) (s : Finset I) :
    ∏ i ∈ s, t ^ w i = t ^ (∑ i ∈ s, w i) := by
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty, zpow_zero]
  | @insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, _root_.zpow_add]

def diagonalWeightSL (K : Type) [Field K] {n : ℕ} (w : Fin n → ℤ)
    (hw : ∑ i, w i = 0) (t : Kˣ) : Algebraic.SL n K :=
  ⟨Matrix.diagonal (fun i => ((t ^ w i : Kˣ) : K)), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, prod_unit_zpow_sum, hw, zpow_zero, Units.val_one]⟩

def diagonalWeightHom (K : Type) [Field K] {n : ℕ} (w : Fin n → ℤ)
    (hw : ∑ i, w i = 0) : Kˣ →* Algebraic.SL n K where
  toFun := diagonalWeightSL K w hw
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (((1 : Kˣ) ^ w i : Kˣ) : K)) = 1
    simp only [_root_.one_zpow, Units.val_one, Matrix.diagonal_one]
  map_mul' s t := by
    apply Subtype.ext
    change Matrix.diagonal (fun i => (((s * t) ^ w i : Kˣ) : K)) =
      Matrix.diagonal (fun i => ((s ^ w i : Kˣ) : K)) * Matrix.diagonal (fun i => ((t ^ w i : Kˣ) : K))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_zpow, Units.val_mul]

def integerPowerPair (k : Type) [Field k] : ℤ → MvPolynomial (Fin 2) k
  | .ofNat n => X 0 ^ n
  | .negSucc n => X 1 ^ (n + 1)

theorem eval_integerPowerPair {k K : Type} [Field k] [Field K]
    (v : k →+* K) (t : Kˣ) (z : ℤ) :
    MvPolynomial.eval₂Hom v (fun i : Fin 2 => if i = 0 then (t : K) else ((t⁻¹ : Kˣ) : K))
      (integerPowerPair k z) = ((t ^ z : Kˣ) : K) := by
  cases z with
  | ofNat n => simp [integerPowerPair]
  | negSucc n => simp [integerPowerPair, zpow_negSucc, inv_pow]

theorem integer_diagonal_trace_zero_weights
    {k : Type} [Field k] [CharZero k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (w : Fin n → ℤ)
    (hw : Matrix.diagonal (fun i => (w i : k)) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∑ i, w i = 0 := by
  have ht := Infinitesimal.Trace.Construction.infinitesimalStabilizer_trace_zero G hw
  apply Int.cast_injective (α := k)
  simpa only [Matrix.trace_diagonal, Int.cast_sum, Int.cast_zero] using ht

end

/-! Integer diagonal infinitesimal matrices integrate to actual
algebraic one-parameter subgroups over every field extension. -/

open scoped Classical
open _root_.Matrix _root_.MvPolynomial

theorem integer_weight_component_mem_vanishingIdeal
    {k : Type} [Field k] [CharZero k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (w : Fin n → ℤ) (hw : Matrix.diagonal (fun i => (w i : k)) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G) (z : ℤ) :
    weightedHomogeneousComponent (fun ij : Fin n × Fin n => w ij.2) z p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G := by
  apply IntegerWeightComponents.Construction.integerWeightComponent_mem_of_invariant (fun ij : Fin n × Fin n => w ij.2)
    ((VanishingIdeal.Construction.coordinateVanishingIdeal G).restrictScalars k) ?_ hp z
  intro q hq
  rw [← IntegerWeightDerivation.Construction.rightInfinitesimal_integer_diagonal]
  exact (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G _).mp hw q hq

theorem evaluate_diagonalWeightSL_homogeneous
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (v : k →+* K) (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (t : Kˣ)
    (p : Algebraic.CoordinatePolynomial n k) (z : ℤ)
    (hp : p.IsWeightedHomogeneous (fun ij : Fin n × Fin n => w ij.2) z) :
    Algebraic.evaluateMatrix v (diagonalWeightSL K w hw t) p =
      ((t ^ z : Kˣ) : K) * Algebraic.evaluateMatrix v (1 : Algebraic.SL n K) p := by
  have he : (fun ij : Fin n × Fin n => diagonalWeightSL K w hw t ij.1 ij.2) =
      fun ij : Fin n × Fin n => ((t ^ w ij.2 : Kˣ) : K) * (1 : Matrix (Fin n) (Fin n) K) ij.1 ij.2 := by
    funext ij
    simp only [diagonalWeightSL, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs with h
    · simp only [h, mul_one]
    · exact (mul_zero _).symm
  change MvPolynomial.eval₂Hom v _ p = _
  rw [he]
  exact IntegerWeightComponents.Construction.eval_integer_scaled_homogeneous v t (fun ij : Fin n × Fin n => w ij.2)
    (fun ij => (1 : Matrix (Fin n) (Fin n) K) ij.1 ij.2) p z hp

theorem diagonalWeightSL_mem_group
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (w : Fin n → ℤ)
    (hw : Matrix.diagonal (fun i => (w i : k)) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (v : k →+* K) (t : Kˣ) :
    diagonalWeightSL K w (integer_diagonal_trace_zero_weights G w hw) t ∈ G.subgroup K v := by
  apply (VanishingIdeal.Construction.mem_group_iff_vanishingIdeal G v _).mpr
  intro p hp
  let weight := fun ij : Fin n × Fin n => w ij.2
  conv_lhs => rw [← IntegerWeightComponents.Construction.sum_integerWeightComponents weight p]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro z _
  rw [evaluate_diagonalWeightSL_homogeneous v w _ t _ z
    (weightedHomogeneousComponent_isWeightedHomogeneous z p)]
  have hz := integer_weight_component_mem_vanishingIdeal G w hw hp z K v (1 : G.Points v)
  change Algebraic.evaluateMatrix v (1 : Algebraic.SL n K)
    (weightedHomogeneousComponent (fun ij : Fin n × Fin n => w ij.2) z p) = 0 at hz
  rw [hz, mul_zero]

def diagonalInfinitesimalCocharacter
    {k : Type} [Field k] [CharZero k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (w : Fin n → ℤ) (hw : Matrix.diagonal (fun i => (w i : k)) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    G.Cocharacter where
  hom K _ v := (diagonalWeightHom K w (integer_diagonal_trace_zero_weights G w hw)).codRestrict
    (G.subgroup K v) (diagonalWeightSL_mem_group G w hw v)
  coordinates i j := if i = j then integerPowerPair k (w i) else 0
  coordinate_eq K _ v t i j := by
    change Matrix.diagonal (fun i => ((t ^ w i : Kˣ) : K)) i j = _
    simp only [Matrix.diagonal_apply]
    split_ifs with h
    · exact (eval_integerPowerPair v t (w i)).symm
    · exact (map_zero _).symm

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalWeightIntegration.Construction
