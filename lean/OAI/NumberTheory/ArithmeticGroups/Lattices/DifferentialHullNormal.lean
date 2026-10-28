import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialDerivationCore
import OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialConjugation
import OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullGroup

/-! # Differential Hull Normal -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullNormal.Construction

noncomputable section

/-! A matrix family stable under conjugation has a normal algebraic
hull inside the matrix group. -/

open scoped Classical

theorem polynomialConjugation_mem_core
    {k : Type} [Field k] {n : ℕ} (S : Set (Matrix (Fin n) (Fin n) k)) (g : Algebraic.SL n k)
    (hS : ∀ A ∈ S, (g : Matrix (Fin n) (Fin n) k) * A *
      ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S)
    {p : Algebraic.CoordinatePolynomial n k} (hp : p ∈ MatrixDifferential.Construction.matrixDifferentialCore S) :
    PolynomialConjugation.Construction.polynomialConjugation g p ∈ MatrixDifferential.Construction.matrixDifferentialCore S := by
  apply DifferentialDerivationCore.Construction.differentialCore_map_mem (Infinitesimal.Action.Construction.rightInfinitesimal '' S)
    (RingHom.ker (Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k))) (PolynomialConjugation.Construction.polynomialConjugation g) _ _ hp
  · intro q hq
    change Algebraic.evaluateMatrix (RingHom.id k) (1 : Algebraic.SL n k) (PolynomialConjugation.Construction.polynomialConjugation g q) = 0
    rw [PolynomialConjugation.Construction.evaluate_polynomialConjugation, mul_one, mul_inv_cancel]
    exact hq
  · rintro D ⟨A, hA, rfl⟩
    refine ⟨Infinitesimal.Action.Construction.rightInfinitesimal ((g : Matrix (Fin n) (Fin n) k) * A *
      ((g⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k)),
      ⟨_, hS A hA, rfl⟩, ?_⟩
    exact PolynomialConjugation.Construction.derivative_polynomialConjugation g A

theorem differentialHull_normal
    {k : Type} [Field k] {n : ℕ} (G : Algebraic.MatrixAlgebraicGroup k n)
    (S : Set (Matrix (Fin n) (Fin n) k))
    (hS : ∀ g : G.RationalPoints, ∀ A ∈ S,
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g.val⁻¹ : Algebraic.SL n k) : Matrix (Fin n) (Fin n) k) ∈ S) :
    (DifferentialHullGroup.Construction.differentialHullSubgroup G S).Normal := by
  constructor
  intro x hx g p hp
  have hc := polynomialConjugation_mem_core S g.val (hS g) hp
  have he := hx (PolynomialConjugation.Construction.polynomialConjugation g.val p) hc
  rw [PolynomialConjugation.Construction.evaluate_polynomialConjugation] at he
  exact he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DifferentialHullNormal.Construction
