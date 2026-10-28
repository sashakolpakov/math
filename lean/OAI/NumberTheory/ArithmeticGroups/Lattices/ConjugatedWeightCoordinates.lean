import OAI.NumberTheory.ArithmeticGroups.Lattices.DiagonalWeightIntegration
import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialConjugation

/-! # Conjugated Weight Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCoordinates.Construction

noncomputable section

section

/-! Integer weight integration in a rationally conjugated basis. The
translated vanishing subspace is stable under the diagonal Euler
derivation and all of its weight components vanish at the identity. -/

open scoped Classical
open _root_.Matrix _root_.MvPolynomial

theorem evaluate_polynomialConjugation_base
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (v : k →+* K) (b : Algebraic.SL n k) (x : Algebraic.SL n K) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix v x (PolynomialConjugation.Construction.polynomialConjugation b p) =
      Algebraic.evaluateMatrix v (Matrix.SpecialLinearGroup.map v b * x * (Matrix.SpecialLinearGroup.map v b)⁻¹) p := by
  change Algebraic.evaluateMatrix v x
    (LeftTranslation.Construction.leftTranslate (b : Matrix (Fin n) (Fin n) k)
      (PolynomialAction.Construction.rightTranslate ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) p)) = _
  rw [LeftTranslation.Construction.leftTranslate_evaluate, PolynomialAction.Construction.rightTranslate_evaluate, map_inv]

def conjugatedVanishingSubspace
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n) (b : Algebraic.SL n k) :
    Submodule k (Algebraic.CoordinatePolynomial n k) :=
  ((VanishingIdeal.Construction.coordinateVanishingIdeal G).restrictScalars k).map (PolynomialConjugation.Construction.polynomialConjugation b).toLinearMap

theorem conjugatedVanishingSubspace_integer_weight_stable
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (b : Algebraic.SL n k) (w : Fin n → ℤ)
    (hw : (b : Matrix (Fin n) (Fin n) k) * Matrix.diagonal (fun i => (w i : k)) *
      ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) :
    ∀ p ∈ conjugatedVanishingSubspace G b,
      IntegerWeightDerivation.Construction.integerWeightDerivation (fun ij : Fin n × Fin n => w ij.2) p ∈ conjugatedVanishingSubspace G b := by
  rintro _ ⟨p, hp, rfl⟩
  change IntegerWeightDerivation.Construction.integerWeightDerivation _ (PolynomialConjugation.Construction.polynomialConjugation b p) ∈ _
  rw [← IntegerWeightDerivation.Construction.rightInfinitesimal_integer_diagonal, PolynomialConjugation.Construction.derivative_polynomialConjugation]
  exact ⟨_, (Infinitesimal.Action.Construction.mem_infinitesimalStabilizer G _).mp hw p hp, rfl⟩

theorem conjugatedVanishingSubspace_evaluate_one
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Algebraic.SL n k) (v : k →+* K)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ conjugatedVanishingSubspace G b) :
    Algebraic.evaluateMatrix v (1 : Algebraic.SL n K) p = 0 := by
  obtain ⟨q, hq, rfl⟩ := hp
  change Algebraic.evaluateMatrix v (1 : Algebraic.SL n K) (PolynomialConjugation.Construction.polynomialConjugation b q) = 0
  rw [evaluate_polynomialConjugation_base, mul_one, mul_inv_cancel]
  exact hq K v (1 : G.Points v)

theorem diagonalWeightSL_vanishes_of_invariant_subspace
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (v : k →+* K) (w : Fin n → ℤ) (hw : ∑ i, w i = 0) (t : Kˣ)
    (W : Submodule k (Algebraic.CoordinatePolynomial n k))
    (hW : ∀ p ∈ W, IntegerWeightDerivation.Construction.integerWeightDerivation (fun ij : Fin n × Fin n => w ij.2) p ∈ W)
    (hone : ∀ p ∈ W, Algebraic.evaluateMatrix v (1 : Algebraic.SL n K) p = 0)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ W) :
    Algebraic.evaluateMatrix v (DiagonalWeightIntegration.Construction.diagonalWeightSL K w hw t) p = 0 := by
  let weight := fun ij : Fin n × Fin n => w ij.2
  conv_lhs => rw [← IntegerWeightComponents.Construction.sum_integerWeightComponents weight p]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro z _
  rw [DiagonalWeightIntegration.Construction.evaluate_diagonalWeightSL_homogeneous v w hw t _ z
    (weightedHomogeneousComponent_isWeightedHomogeneous z p),
    hone _ (IntegerWeightComponents.Construction.integerWeightComponent_mem_of_invariant weight W hW hp z), mul_zero]

theorem conjugate_diagonalWeightSL_mem_group
    {k K : Type} [Field k] [CharZero k] [Field K] {n : ℕ}
    (G : Algebraic.MatrixAlgebraicGroup k n) (b : Algebraic.SL n k) (w : Fin n → ℤ)
    (hsum : ∑ i, w i = 0)
    (hw : (b : Matrix (Fin n) (Fin n) k) * Matrix.diagonal (fun i => (w i : k)) *
      ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G)
    (v : k →+* K) (t : Kˣ) :
    Matrix.SpecialLinearGroup.map v b * DiagonalWeightIntegration.Construction.diagonalWeightSL K w hsum t * (Matrix.SpecialLinearGroup.map v b)⁻¹ ∈
      G.subgroup K v := by
  apply (VanishingIdeal.Construction.mem_group_iff_vanishingIdeal G v _).mpr
  intro p hp
  rw [← evaluate_polynomialConjugation_base]
  exact diagonalWeightSL_vanishes_of_invariant_subspace v w hsum t
    (conjugatedVanishingSubspace G b) (conjugatedVanishingSubspace_integer_weight_stable G b w hw)
    (fun _ hq => conjugatedVanishingSubspace_evaluate_one G b v hq) ⟨p, hp, rfl⟩

end

/-! Regular two-variable coordinates for rationally conjugated
integer-weight matrix homomorphisms. -/

open scoped Classical
open _root_.Matrix _root_.MvPolynomial

def conjugatedWeightCoordinates
    {k : Type} [Field k] {n : ℕ} (b : Algebraic.SL n k) (w : Fin n → ℤ) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin 2) k) :=
  (b : Matrix (Fin n) (Fin n) k).map MvPolynomial.C * Matrix.diagonal (fun i => DiagonalWeightIntegration.Construction.integerPowerPair k (w i)) *
    ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k).map MvPolynomial.C

theorem evaluate_conjugatedWeightCoordinates
    {k K : Type} [Field k] [Field K] {n : ℕ}
    (v : k →+* K) (b : Algebraic.SL n k) (w : Fin n → ℤ) (hsum : ∑ i, w i = 0) (t : Kˣ) :
    (MvPolynomial.eval₂Hom v (fun i : Fin 2 => if i = 0 then (t : K) else ((t⁻¹ : Kˣ) : K))).mapMatrix
        (conjugatedWeightCoordinates b w) =
      ((Matrix.SpecialLinearGroup.map v b * DiagonalWeightIntegration.Construction.diagonalWeightSL K w hsum t *
        (Matrix.SpecialLinearGroup.map v b)⁻¹ : Algebraic.SL n K) : Matrix (Fin n) (Fin n) K) := by
  let ev := MvPolynomial.eval₂Hom v (fun i : Fin 2 => if i = 0 then (t : K) else ((t⁻¹ : Kˣ) : K))
  have heC (A : Matrix (Fin n) (Fin n) k) : ev.mapMatrix (A.map MvPolynomial.C) = A.map v := by
    ext i j
    exact MvPolynomial.eval₂_C _ _ _
  have heD : ev.mapMatrix (Matrix.diagonal (fun i => DiagonalWeightIntegration.Construction.integerPowerPair k (w i))) =
      Matrix.diagonal (fun i => ((t ^ w i : Kˣ) : K)) := by
    ext i j
    change ev (if i = j then DiagonalWeightIntegration.Construction.integerPowerPair k (w i) else 0) =
      if i = j then ((t ^ w i : Kˣ) : K) else 0
    split_ifs
    · exact DiagonalWeightIntegration.Construction.eval_integerPowerPair v t (w i)
    · exact map_zero ev
  change ev.mapMatrix (_ * _ * _) = _
  rw [map_mul, map_mul, heC, heC, heD]
  rw [← map_inv]
  rfl

theorem conjugated_integer_diagonal_trace_zero_weights
    {k : Type} [Field k] [CharZero k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (b : Algebraic.SL n k) (w : Fin n → ℤ)
    (hw : (b : Matrix (Fin n) (Fin n) k) * Matrix.diagonal (fun i => (w i : k)) *
      ((b⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ Infinitesimal.Action.Construction.infinitesimalStabilizer G) : ∑ i, w i = 0 := by
  have ht := Infinitesimal.Trace.Construction.infinitesimalStabilizer_trace_zero G hw
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, Matrix.trace_diagonal] at ht
  apply Int.cast_injective (α := k)
  simpa only [Int.cast_sum, Int.cast_zero] using ht

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ConjugatedWeightCoordinates.Construction
