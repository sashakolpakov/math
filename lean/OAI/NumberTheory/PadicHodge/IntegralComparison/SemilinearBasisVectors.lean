import Mathlib.LinearAlgebra.Basis.Defs

/-! # Semilinear Basis Vectors -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SemilinearBasisVectors

noncomputable section

/-!
# IntegralComparison: a semilinear map on finite basis expansions
-/

universe u v w z t

variable {R : Type u} {S : Type v} [Semiring R] [Semiring S]
  {M : Type w} {N : Type z} [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module S N]
  {ι : Type t} [Fintype ι]

theorem map_vectors (φ : R →+* S) (f : M →+ N)
    (hf : ∀ r m, f (r • m) = φ r • f m)
    (b : Module.Basis ι R M) (c : Module.Basis ι S N) (hb : ∀ i, f (b i) = c i) (x : ι → R) :
    f (b.equivFun.symm x) = c.equivFun.symm (fun i => φ (x i)) := by
  rw [Module.Basis.equivFun_symm_apply, map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (hf (x i) (b i)).trans (congrArg (fun m => φ (x i) • m) (hb i))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SemilinearBasisVectors
