import OAI.NumberTheory.Quaternion.Arithmetic.AdjointPolynomials
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Adjoint Closed -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.AdjointClosed

noncomputable section

/-! Membership of a conjugated matrix in a fixed linear subspace is a
Zariski-closed condition on the conjugating algebraic-group point. -/

open scoped Classical
open Set

variable {k : Type} [Field k] {n : ℕ} (G : ArithmeticGroups.Lattices.Algebraic.MatrixAlgebraicGroup k n)

local instance adjointClosedRationalTopology : TopologicalSpace G.RationalPoints := ArithmeticGroups.Lattices.RationalZariski.Construction.rationalZariskiTopology G

theorem rational_adjoint_subspace_closed
    (A : Matrix (Fin n) (Fin n) k) (W : Submodule k (Matrix (Fin n) (Fin n) k)) :
    IsClosed {g : G.RationalPoints |
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g⁻¹).val : Matrix (Fin n) (Fin n) k) ∈ W} := by
  have he : {g : G.RationalPoints |
      (g.val : Matrix (Fin n) (Fin n) k) * A *
        ((g⁻¹).val : Matrix (Fin n) (Fin n) k) ∈ W} =
      ⋂ φ : W.dualAnnihilator, {g : G.RationalPoints |
        ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g.val
          (AdjointPolynomials.linearMatrixPolynomial φ.val (AdjointPolynomials.adjointMatrixPolynomial A)) = 0} := by
    ext g
    simp only [mem_iInter, mem_ofPred_eq, AdjointPolynomials.evaluate_linearMatrixPolynomial,
      AdjointPolynomials.evaluate_adjointMatrixPolynomial]
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W]
    exact ⟨fun h φ => h φ.val φ.property, fun h φ hφ => h ⟨φ, hφ⟩⟩
  rw [he]
  exact isClosed_iInter (fun φ => ArithmeticGroups.Lattices.RationalZariski.Construction.rational_polynomial_zero_closed G _)

theorem rational_inverse_continuous : Continuous (fun g : G.RationalPoints => g⁻¹) := by
  let Xmat : Matrix (Fin n) (Fin n) (ArithmeticGroups.Lattices.Algebraic.CoordinatePolynomial n k) :=
    fun i j => MvPolynomial.X (i, j)
  apply ArithmeticGroups.Lattices.RationalZariski.Construction.rational_polynomial_map_continuous G _ (fun ij => Xmat.adjugate ij.1 ij.2)
  intro g i j
  let e := ArithmeticGroups.Lattices.Algebraic.evaluateMatrix (RingHom.id k) g.val
  have hX : e.mapMatrix Xmat = (g.val : Matrix (Fin n) (Fin n) k) := by
    ext a b
    change e (MvPolynomial.X (a, b)) = g.val a b
    simp [e, ArithmeticGroups.Lattices.Algebraic.evaluateMatrix]
  have he := e.map_adjugate Xmat
  rw [hX] at he
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) k => M i j)
    he
  exact h.symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.AdjointClosed
