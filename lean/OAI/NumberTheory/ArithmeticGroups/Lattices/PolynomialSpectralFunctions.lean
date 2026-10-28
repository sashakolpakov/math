import OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisSemisimple
import Mathlib.LinearAlgebra.Lagrange

/-! # Polynomial Spectral Functions -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialSpectralFunctions.Construction

noncomputable section

/-! A function of the eigenvalues of a finite eigenbasis is a polynomial
in the original endomorphism, and therefore preserves its invariant subspaces. -/

open scoped Classical

theorem eigenvalue_function_is_polynomial
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (b : Module.Basis ι k V) (f g : Module.End k V) (eigenvalue : ι → k) (ψ : k → k)
    (hf : ∀ i, f (b i) = eigenvalue i • b i)
    (hg : ∀ i, g (b i) = ψ (eigenvalue i) • b i) :
    ∃ p : Polynomial k, Polynomial.aeval f p = g := by
  obtain ⟨p, hp⟩ := (Polynomial.exists_eval_eq_iff eigenvalue (ψ ∘ eigenvalue)).mpr
    (fun i j hij => congrArg ψ hij)
  refine ⟨p, b.ext fun i => ?_⟩
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hf i), hp i, hg i]
  rfl

theorem eigenvalue_function_preserves_submodule
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (b : Module.Basis ι k V) (f g : Module.End k V) (eigenvalue : ι → k) (ψ : k → k)
    (hf : ∀ i, f (b i) = eigenvalue i • b i)
    (hg : ∀ i, g (b i) = ψ (eigenvalue i) • b i)
    (W : Submodule k V) (hW : W ≤ W.comap f) : W ≤ W.comap g := by
  obtain ⟨p, rfl⟩ := eigenvalue_function_is_polynomial b f g eigenvalue ψ hf hg
  exact fun _ hx => Polynomial.aeval_apply_smul_mem_of_le_comap hx p f hW

theorem eigenvalue_function_on_eigenvector
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (b : Module.Basis ι k V) (f g : Module.End k V) (eigenvalue : ι → k) (ψ : k → k)
    (hf : ∀ i, f (b i) = eigenvalue i • b i)
    (hg : ∀ i, g (b i) = ψ (eigenvalue i) • b i)
    (x : V) (a : k) (hx : f x = a • x) : g x = ψ a • x := by
  let values : Option ι → k := Option.elim' a eigenvalue
  obtain ⟨p, hp⟩ := (Polynomial.exists_eval_eq_iff values (ψ ∘ values)).mpr
    (fun i j hij => congrArg ψ hij)
  have hpi (i : ι) : p.eval (eigenvalue i) = ψ (eigenvalue i) := hp (some i)
  have hpa : p.eval a = ψ a := hp none
  have heq : Polynomial.aeval f p = g := by
    apply b.ext
    intro i
    rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hf i), hpi i, hg i]
  rw [← heq, Module.End.aeval_apply_of_mem_apply_eq_smul hx, hpa]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolynomialSpectralFunctions.Construction
