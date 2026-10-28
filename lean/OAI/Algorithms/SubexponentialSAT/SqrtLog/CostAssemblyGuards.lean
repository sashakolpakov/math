import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram
import OAI.Algorithms.SubexponentialSAT.SqrtLog.AsymptoticResidualLayout

namespace OAI.Algorithms

/-! Uniform large-input success of the actual integer parameter guards.
The cutoff is selected before the produced input.  The nonempty-formula and
neutral-coverage premises are explicit semantic obligations of the caller. -/
namespace SubexponentialSAT.SqrtLog.CostAssembly

open Filter
open scoped Topology
open LeafParametersProgram

theorem eventually_parameter_guards (q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Input,
      x.ambient = n → x.freeCount ≤ n → n ≤ 2*x.freeCount →
      0 < x.clauses → 0 < x.occurrence → 0 < x.arity →
      x.freeCount ≤ x.incidences →
      x.occurrence ≤ Asymptotic.L x.freeCount^q →
      x.arity ≤ Asymptotic.L x.freeCount^q → Guard x := by
  filter_upwards [Asymptotic.eventually_residual_layout_guards q,
    eventually_ge_atTop (2 : ℕ)] with n hn hnpos x hamb hfree hhalf hcl hb ha hM hbp hap
  obtain ⟨hQ,hR,hsmall,hlarge⟩ := hn x.freeCount x.arity x.occurrence hhalf hap hbp
  refine ⟨by omega,by simpa only [hamb] using hfree,hcl,hb,ha,hM,hQ,hR,?_,hsmall⟩
  calc
    4*(x.occurrence+x.arity)*(produce x).N^2*(produce x).epsilonDen^2 =
        4096*(x.occurrence+x.arity)*x.occurrence^2*
          Asymptotic.layoutR x.freeCount^2*Asymptotic.L x.freeCount^4*
          (Asymptotic.layoutR x.freeCount^(2*Asymptotic.layoutQ x.freeCount))^2 := by
      dsimp [produce]
      ring
    _ ≤ x.freeCount := hlarge
    _ ≤ x.incidences := hM

/-- One cutoff handles every branch-dependent produced parameter record.
The numerical factor count and width are unrestricted here: they affect the
jet order but do not occur in the executable feasibility guard. -/
theorem parameter_guards_uniform_cutoff (q : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Input,
      x.ambient = n → x.freeCount ≤ n → n ≤ 2*x.freeCount →
      0 < x.clauses → 0 < x.occurrence → 0 < x.arity →
      x.freeCount ≤ x.incidences →
      x.occurrence ≤ Asymptotic.L x.freeCount^q →
      x.arity ≤ Asymptotic.L x.freeCount^q →
      Guard x ∧ passes x = true ∧ dispatch x = .sparse := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (eventually_parameter_guards q)
  refine ⟨N,?_⟩
  intro n hn x hamb hfree hhalf hcl hb ha hM hbp hap
  have h := hN n hn x hamb hfree hhalf hcl hb ha hM hbp hap
  exact ⟨h,(passes_eq_true x).2 h,(dispatch_sparse_iff x).2 h⟩

/-- Fixed ambient polylogarithmic scope bounds suffice for every retained-half
branch.  No choice of a branch or formula precedes the cutoff. -/
theorem eventually_parameter_guards_ambient (C q : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ x : Input,
      x.ambient = n → x.freeCount ≤ n → n ≤ 2*x.freeCount →
      0 < x.clauses → 0 < x.occurrence → 0 < x.arity →
      x.freeCount ≤ x.incidences →
      x.occurrence ≤ C*Asymptotic.L n^q →
      x.arity ≤ C*Asymptotic.L n^q → Guard x := by
  filter_upwards [eventually_parameter_guards (q+1),
    Asymptotic.eventually_residual_polynomial C q] with n hn hp x hamb hfree hhalf
      hcl hb ha hM hbp hap
  exact hn x hamb hfree hhalf hcl hb ha hM
    (hp x.freeCount x.occurrence hhalf hbp) (hp x.freeCount x.arity hhalf hap)

theorem parameter_guards_ambient_uniform_cutoff (C q : ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : Input,
      x.ambient = n → x.freeCount ≤ n → n ≤ 2*x.freeCount →
      0 < x.clauses → 0 < x.occurrence → 0 < x.arity →
      x.freeCount ≤ x.incidences →
      x.occurrence ≤ C*Asymptotic.L n^q →
      x.arity ≤ C*Asymptotic.L n^q →
      Guard x ∧ passes x = true ∧ dispatch x = .sparse := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp (eventually_parameter_guards_ambient C q)
  refine ⟨N,?_⟩
  intro n hn x hamb hfree hhalf hcl hb ha hM hbp hap
  have h := hN n hn x hamb hfree hhalf hcl hb ha hM hbp hap
  exact ⟨h,(passes_eq_true x).2 h,(dispatch_sparse_iff x).2 h⟩

end SubexponentialSAT.SqrtLog.CostAssembly

end OAI.Algorithms
