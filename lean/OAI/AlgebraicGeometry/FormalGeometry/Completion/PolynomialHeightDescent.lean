import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialQuadratic
import OAI.AlgebraicGeometry.FormalGeometry.Completion.QuadraticQuotientDescent

/-! # Polynomial Height Descent -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion

noncomputable section

/-! A bounded-degree positive polynomial invariant with quadratic top
coefficients and finite reductions forces finite generation. Each zero
subgroup lowers the polynomial degree; no single coefficient is assumed definite. -/

universe u

theorem PolynomialQuadratic.Construction.PolynomialQuadraticHeight.finiteGenerated_of_kernel {G : Type u} [AddCommGroup G]
    (q : PolynomialQuadratic.Construction.PolynomialQuadraticHeight G) (d : ℕ) (hd : ∀ x, (q.value x).natDegree ≤ d)
    [AddGroup.FG (q.coefficientQuadratic d hd).zeroKernel]
    (n : ℕ) (hn : 2 ≤ n)
    (hfinite : ∀ r : ℕ, Finite (G ⧸ (nsmulAddMonoidHom (n ^ r) : G →+ G).range)) :
    AddGroup.FG G := by
  have : AddGroup.FG (G ⧸ (q.coefficientQuadratic d hd).zeroKernel) :=
    (q.coefficientQuadratic d hd).quotient_finiteGenerated d.factorial (Nat.factorial_pos d)
      (q.coefficient_integral d hd) n hn hfinite
  exact QuadraticQuotientDescent.Construction.addGroup_finiteGenerated_of_subgroup_quotient (q.coefficientQuadratic d hd).zeroKernel

theorem PolynomialQuadratic.Construction.PolynomialQuadraticHeight.finiteGenerated_of_degree_bound (d : ℕ) :
    ∀ {G : Type u} [AddCommGroup G] (q : PolynomialQuadratic.Construction.PolynomialQuadraticHeight G)
      (_hd : ∀ x, (q.value x).natDegree ≤ d) (n : ℕ) (_hn : 2 ≤ n)
      (_hfinite : ∀ r : ℕ, Finite (G ⧸ (nsmulAddMonoidHom (n ^ r) : G →+ G).range)), AddGroup.FG G := by
  induction d with
  | zero =>
    intro G _ q hd n hn hfinite
    have : Subsingleton (q.coefficientQuadratic 0 hd).zeroKernel := q.zero_degree_kernel_subsingleton hd
    have : Finite (q.coefficientQuadratic 0 hd).zeroKernel := inferInstance
    have : AddGroup.FG (q.coefficientQuadratic 0 hd).zeroKernel := AddGroup.fg_of_finite
    exact q.finiteGenerated_of_kernel 0 hd n hn hfinite
  | succ d ih =>
    intro G _ q hd n hn hfinite
    let Q := q.coefficientQuadratic (d + 1) hd
    have hk : ∀ x : Q.zeroKernel, ((q.restrict Q.zeroKernel).value x).natDegree ≤ d :=
      q.kernel_degree_bound d hd
    have hf : ∀ r : ℕ, Finite (Q.zeroKernel ⧸
        (nsmulAddMonoidHom (n ^ r) : Q.zeroKernel →+ Q.zeroKernel).range) := by
      intro r
      have := hfinite r
      exact Completion.Finite.ReductionTransport.Construction.finite_nsmulQuotient_of_saturated Q.zeroKernel (n ^ r)
        (fun x hx => (Q.nsmul_mem_zeroKernel_iff (n ^ r) (pow_pos (by omega) r) x).mp hx)
    have : AddGroup.FG Q.zeroKernel := ih (q.restrict Q.zeroKernel) hk n hn hf
    exact q.finiteGenerated_of_kernel (d + 1) hd n hn hfinite

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion
