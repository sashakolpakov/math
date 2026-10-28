import OAI.NumberTheory.ArithmeticGroups.Lattices.Infinitesimal.Action

/-! # Exponential Polynomial -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialPolynomial.Construction

noncomputable section

/-! Polynomial functions along matrix exponential curves and their
infinitesimal derivatives. -/

open scoped Classical _root_.Matrix.Norms.Operator
open _root_.MvPolynomial NormedSpace

variable {k : Type} [RCLike k] {n : ℕ}

def exponentialPolynomial (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) : k → k :=
  fun t => MvPolynomial.eval (fun ij => exp (t • A) ij.1 ij.2) p

def matrixEntryCLM (i j : Fin n) : Matrix (Fin n) (Fin n) k →L[k] k :=
  (show Matrix (Fin n) (Fin n) k →ₗ[k] k from
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap

theorem matrix_exp_entry_hasDerivAt (A : Matrix (Fin n) (Fin n) k)
    (t : k) (i j : Fin n) :
    HasDerivAt (fun s : k => exp (s • A) i j) ((exp (t • A) * A) i j) t := by
  exact (matrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const A t)

theorem matrix_exp_entry_analyticAt (A : Matrix (Fin n) (Fin n) k)
    (t : k) (i j : Fin n) :
    AnalyticAt k (fun s : k => exp (s • A) i j) t := by
  have hs : AnalyticAt k (fun s : k => s • A) t :=
    (analyticAt_id (𝕜 := k) (z := t)).smul analyticAt_const
  have he : AnalyticAt k (fun s : k => exp (s • A)) t :=
    (NormedSpace.exp_analytic (𝕂 := k) (t • A)).comp (f := fun s : k => s • A) hs
  exact ((matrixEntryCLM i j).analyticAt _).comp (f := fun s : k => exp (s • A)) he

theorem exponentialPolynomial_hasDerivAt (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) (t : k) :
    HasDerivAt (exponentialPolynomial A p)
      (exponentialPolynomial A (Infinitesimal.Action.Construction.rightInfinitesimal A p) t) t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    unfold exponentialPolynomial
    simpa using (hasDerivAt_const t c)
  | add p q hp hq =>
    unfold exponentialPolynomial at hp hq ⊢
    simpa only [map_add, Pi.add_def] using hp.add hq
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    have hX := matrix_exp_entry_hasDerivAt A t i j
    unfold exponentialPolynomial at hp ⊢
    convert! hp.mul hX using 1
    · simp only [map_mul, eval_X]
      rfl
    · simp only [Derivation.leibniz, smul_eq_mul,
        Infinitesimal.Action.Construction.rightInfinitesimal_X, map_add, map_mul, map_sum, eval_X, eval_C, Matrix.mul_apply]
      ring

theorem exponentialPolynomial_analyticAt (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) (t : k) :
    AnalyticAt k (exponentialPolynomial A p) t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    unfold exponentialPolynomial
    simpa using (analyticAt_const (𝕜 := k) (v := c))
  | add p q hp hq =>
    unfold exponentialPolynomial at hp hq ⊢
    simpa only [map_add, Pi.add_def] using hp.add hq
  | mul_X p ij hp =>
    obtain ⟨i, j⟩ := ij
    unfold exponentialPolynomial at hp ⊢
    simpa only [map_mul, eval_X, Pi.mul_def] using hp.mul (matrix_exp_entry_analyticAt A t i j)

theorem exponentialPolynomial_deriv (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) :
    deriv (exponentialPolynomial A p) = exponentialPolynomial A (Infinitesimal.Action.Construction.rightInfinitesimal A p) := by
  funext t
  exact (exponentialPolynomial_hasDerivAt A p t).deriv

theorem exponentialPolynomial_iteratedDeriv (A : Matrix (Fin n) (Fin n) k)
    (p : Algebraic.CoordinatePolynomial n k) (r : ℕ) :
    iteratedDeriv r (exponentialPolynomial A p) =
      exponentialPolynomial A ((Infinitesimal.Action.Construction.rightInfinitesimal A)^[r] p) := by
  induction r generalizing p with
  | zero => rfl
  | succ r hr =>
    rw [iteratedDeriv_succ', exponentialPolynomial_deriv, hr, Function.iterate_succ_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialPolynomial.Construction
