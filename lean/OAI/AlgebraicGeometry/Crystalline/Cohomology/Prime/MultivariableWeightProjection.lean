import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableKoszul

/-! # Multivariable Weight Projection -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableWeightProjection.PrimeMultivariableWeightProjection

noncomputable section

/-! # The coordinate homotopy retains exactly the Frobenius weights of monomial forms -/

open _root_.CategoryTheory Classical
open scoped TensorProduct

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p] [Fintype σ]

local notation "W" => WittVector p k
local notation "P" => MvPolynomial σ W
local notation "D" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableKoszul.PrimeMultivariableKoszul.derivatives p k σ
local notation "S" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariablePrimitive.PrimeMultivariablePrimitive.primitive p k σ

abbrev word (n : ℕ) (v : Fin n → σ) : ⋀[W]^n (σ →₀ W) :=
  exteriorPower.ιMulti W n (fun j => Finsupp.single (v j) 1)

omit [CharP k p] [Fintype σ] in
theorem present_word (i : σ) (n : ℕ) (v : Fin (n + 1) → σ) :
    Koszul.Tensor.KoszulTensor.exteriorWedge W σ i n (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction W σ i n (word p k σ (n + 1) v)) =
      if i ∈ Set.range v then word p k σ (n + 1) v else 0 := by
  calc
    _ = word p k σ (n + 1) v -
        Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorProjection W σ i (n + 1) (word p k σ (n + 1) v) :=
      (sub_sub_cancel _ _).symm
    _ = _ := by
      rw [ExteriorCoordinate.ExteriorCoordinateProjection.projection_word]
      split_ifs <;> simp

theorem projection_word (i : σ) (n : ℕ) (d : σ →₀ ℕ) (a : W) (v : Fin n → σ) :
    (MultivariableKoszul.PrimeMultivariableKoszul.projection p k σ i).f n
      (MvPolynomial.monomial d a ⊗ₜ[W] word p k σ n v) =
        if p ∣ d i + (if i ∈ Set.range v then 1 else 0)
          then MvPolynomial.monomial d a ⊗ₜ[W] word p k σ n v else 0 := by
  rw [MultivariableKoszul.PrimeMultivariableKoszul.projection_f]
  cases n with
  | zero =>
    change Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection W σ P D i (S i) (MvPolynomial.monomial d a) ⊗ₜ[W]
      word p k σ 0 v = _
    rw [MultivariableKoszul.PrimeMultivariableKoszul.coefficient_zero, MultivariablePrimitive.PrimeMultivariablePrimitive.projection_monomial]
    have hv : ¬ i ∈ Set.range v := by rintro ⟨j, _⟩; exact Fin.elim0 j
    simp only [ite_eq_right hv, Nat.add_zero]
    split_ifs <;> simp only [TensorProduct.zero_tmul]
  | succ n =>
    change Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.coefficientProjection W σ P D i (S i) (MvPolynomial.monomial d a) ⊗ₜ[W]
        Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorProjection W σ i (n + 1) (word p k σ (n + 1) v) +
      Koszul.PartialPrimitive.KoszulPartialPrimitive.projectionOne W σ P D i (S i) (MvPolynomial.monomial d a) ⊗ₜ[W]
        Koszul.Tensor.KoszulTensor.exteriorWedge W σ i n
          (Koszul.CoordinateHomotopy.KoszulCoordinateHomotopy.exteriorContraction W σ i n (word p k σ (n + 1) v)) = _
    rw [MultivariableKoszul.PrimeMultivariableKoszul.coefficient_zero, MultivariableKoszul.PrimeMultivariableKoszul.coefficient_one,
      MultivariablePrimitive.PrimeMultivariablePrimitive.projection_monomial, MultivariablePrimitive.PrimeMultivariablePrimitive.projection_monomial,
      ExteriorCoordinate.ExteriorCoordinateProjection.projection_word, present_word]
    by_cases hi : i ∈ Set.range v
    · simp only [ite_eq_left hi, TensorProduct.tmul_zero, zero_add]
      split_ifs <;> simp only [TensorProduct.zero_tmul]
    · simp only [ite_eq_right hi, TensorProduct.tmul_zero, add_zero]
      split_ifs <;> simp only [TensorProduct.zero_tmul]

theorem successive_word (l : List σ) (n : ℕ) (d : σ →₀ ℕ) (a : W) (v : Fin n → σ) :
    (MultivariableKoszul.PrimeMultivariableKoszul.successive p k σ l).f n
      (MvPolynomial.monomial d a ⊗ₜ[W] word p k σ n v) =
        if ∀ i ∈ l, p ∣ d i + (if i ∈ Set.range v then 1 else 0)
          then MvPolynomial.monomial d a ⊗ₜ[W] word p k σ n v else 0 := by
  induction l with
  | nil => simp [MultivariableKoszul.PrimeMultivariableKoszul.successive, Koszul.SuccessiveHomotopy.KoszulSuccessiveHomotopy.chain]; rfl
  | cons i l ih =>
    change (MultivariableKoszul.PrimeMultivariableKoszul.successive p k σ l).f n
      ((MultivariableKoszul.PrimeMultivariableKoszul.projection p k σ i).f n (MvPolynomial.monomial d a ⊗ₜ[W] word p k σ n v)) = _
    rw [projection_word]
    by_cases hi : p ∣ d i + (if i ∈ Set.range v then 1 else 0)
    · rw [ite_eq_left hi, ih]
      congr 1
      simp only [List.mem_cons, forall_eq_or_imp, hi, true_and]
    · rw [ite_eq_right hi]
      have hn : ¬ ∀ j ∈ i :: l, p ∣ d j + (if j ∈ Set.range v then 1 else 0) := by
        intro h
        exact hi (h i List.mem_cons_self)
      exact (map_zero (show Module.End W (Koszul.Tensor.KoszulTensor.Term W σ P n) from
        ((MultivariableKoszul.PrimeMultivariableKoszul.successive p k σ l).f n).hom)).trans (ite_eq_right hn).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.MultivariableWeightProjection.PrimeMultivariableWeightProjection
