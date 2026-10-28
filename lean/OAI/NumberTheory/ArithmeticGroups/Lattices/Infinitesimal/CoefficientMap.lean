import OAI.NumberTheory.ArithmeticGroups.Lattices.TangentIdentity

/-! # Coefficient Map -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CoefficientMap.Construction

noncomputable section

section

/-! Compatibility of matrix infinitesimal differentiation with extension
of the coefficient field. -/

open scoped Classical
open _root_.MvPolynomial

theorem rightInfinitesimal_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (A : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    Action.Construction.rightInfinitesimal (A.map ι) (MvPolynomial.map ι p) =
      MvPolynomial.map ι (Action.Construction.rightInfinitesimal A p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul, MvPolynomial.map_X, Derivation.leibniz,
        smul_eq_mul, map_add, hp, Action.Construction.rightInfinitesimal_X, map_sum,
        MvPolynomial.map_C, Matrix.map_apply]

theorem evaluate_one_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id K) (1 : Algebraic.SL n K) (MvPolynomial.map ι p) =
      ι (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [Algebraic.evaluateMatrix]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p ij hp =>
      rcases ij with ⟨i, j⟩
      simp only [map_mul, hp]
      congr 1
      simp [Algebraic.evaluateMatrix, Matrix.one_apply]

theorem tangent_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (A : Matrix (Fin n) (Fin n) k) (p : Algebraic.CoordinatePolynomial n k) :
    Algebraic.evaluateMatrix (RingHom.id K) (1 : Algebraic.SL n K)
        (Action.Construction.rightInfinitesimal (A.map ι) (MvPolynomial.map ι p)) =
      ι (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Action.Construction.rightInfinitesimal A p)) := by
  rw [rightInfinitesimal_coefficient_map, evaluate_one_coefficient_map]

end

/-! Polynomials vanishing to first order at the identity form an ideal.
This allows tangent equations to be checked on ideal generators. -/

open scoped Classical

def identityTangentIdeal {k : Type} [Field k] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) k) : Ideal (Algebraic.CoordinatePolynomial n k) where
  carrier := {p | Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) p = 0 ∧
    Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Action.Construction.rightInfinitesimal A p) = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro p q ⟨hp, hp'⟩ ⟨hq, hq'⟩
    simp only [Set.mem_ofPred_eq, map_add, hp, hp', hq, hq', add_zero, and_self]
  smul_mem' := by
    rintro r p ⟨hp, hp'⟩
    change _ = 0 ∧ _ = 0
    simp only [smul_eq_mul, map_mul, Derivation.leibniz, map_add, hp, hp',
      mul_zero, zero_mul, zero_add, and_self]

theorem vanishingIdeal_le_identityTangentIdeal_iff
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (A : Matrix (Fin n) (Fin n) k) :
    VanishingIdeal.Construction.coordinateVanishingIdeal G ≤ identityTangentIdeal A ↔
      ∀ p ∈ VanishingIdeal.Construction.coordinateVanishingIdeal G,
        Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (Action.Construction.rightInfinitesimal A p) = 0 := by
  constructor
  · intro h p hp
    exact (h hp).2
  · intro h p hp
    exact ⟨hp k (RingHom.id k) (1 : G.RationalPoints), h p hp⟩

theorem identityTangentIdeal_coefficient_map
    {k K : Type} [Field k] [Field K] {n : ℕ} (ι : k →+* K)
    (A : Matrix (Fin n) (Fin n) k) :
    (identityTangentIdeal A).map (MvPolynomial.map ι) ≤ identityTangentIdeal (A.map ι) := by
  rw [Ideal.map_le_iff_le_comap]
  intro p hp
  change _ = 0 ∧ _ = 0
  rw [evaluate_one_coefficient_map, tangent_coefficient_map, hp.1, hp.2, map_zero]
  exact ⟨rfl, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.CoefficientMap.Construction
