import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyParameterValuesLayout

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

open LeafParametersProgram LeafParametersProgram.Bank LeafParametersProgram.Circuit


/-- A fixed polynomial envelope for every actual numeric bank entry. It
includes both power outputs and the guard's reused low scratch ports. -/
def envelope (S : ℕ) : ℕ :=
  iter Serialization.code.length (iter GuardSetup.code.length
    (iter Layout.code.length (S+16*(2*S+1)^2+128)))

theorem guarded_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (Execute.guardedModel x l).val j ≤
      iter GuardSetup.code.length (iter Layout.code.length (base x)) := by
  intro j
  dsimp [Execute.guardedModel]
  split
  · exact prepared_le x l j
  · exact Nat.zero_le _

theorem serialization_constants : ∀ i ∈ Serialization.code,Constants i := by
  simp [Serialization.code,Constants]

theorem serialization_powers (B : ℕ) (m : Model) : PowerBounds B Serialization.code m := by
  simp [Serialization.code,PowerBounds,PowerBound]

/-- No positivity, guard, or padding-length premise is needed. -/
theorem serialized_values_le (x : Input) (l : Fin 8 → ℕ) :
    ∀ j, (result Serialization.code (Execute.guardedModel x l)).val j ≤ envelope (magnitude x) :=
  result_le le_rfl _ _ (guarded_le x l) serialization_constants (serialization_powers _ _)

theorem envelope_ordinary : Polynomial.Ordinary envelope := by
  apply iter_ordinary
  apply iter_ordinary
  apply iter_ordinary
  exact Polynomial.ordinary_add
    (Polynomial.ordinary_add Polynomial.ordinary_id
      (Polynomial.ordinary_mul (Polynomial.ordinary_const 16)
        (Polynomial.ordinary_pow
          (Polynomial.ordinary_add
            (Polynomial.ordinary_mul (Polynomial.ordinary_const 2) Polynomial.ordinary_id)
            (Polynomial.ordinary_const 1)) 2)))
    (Polynomial.ordinary_const 128)

/-- Fixed constants are chosen before the input, its padding, and the port. -/
theorem serialized_values_polynomial : ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ)
    (S : ℕ), magnitude x ≤ S → ∀ j,
    (result Serialization.code (Execute.guardedModel x l)).val j ≤ C*(S+1)^d := by
  obtain ⟨C,d,h⟩ := envelope_ordinary
  refine ⟨C,d,?_⟩
  intro x l S hS j
  exact (serialized_values_le x l j).trans ((h _).trans
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) d)))

/-- The actual-query scalar theorem supplies magnitude ≤ n^4. This consequence
keeps all constants uniform over every query and every physical padding. -/
theorem serialized_values_of_fourth_power : ∃ C d : ℕ, ∀ (x : Input) (l : Fin 8 → ℕ)
    (n : ℕ), magnitude x ≤ n^4 → ∀ j,
    (result Serialization.code (Execute.guardedModel x l)).val j ≤ C*(n+1)^d := by
  obtain ⟨C,d,h⟩ := serialized_values_polynomial
  refine ⟨C,4*d,?_⟩
  intro x l n hn j
  have hn4 : n^4+1 ≤ (n+1)^4 := by
    have he : (n+1)^4=n^4+4*n^3+6*n^2+4*n+1 := by ring
    rw [he]
    omega
  calc
    _  ≤  C*(n^4+1)^d := h x l (n^4) hn j
    _  ≤  C*((n+1)^4)^d := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hn4 d)
    _ = _ := by rw [pow_mul]

end SubexponentialSAT.SqrtLog.CostAssembly.ParameterValues

end OAI.Algorithms
