import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Semisimple

/-! # Eigenbasis Semisimple -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisSemisimple.Construction

noncomputable section

/-! A finite eigenbasis gives a squarefree annihilating polynomial. -/

open scoped Classical

theorem isSemisimple_of_finite_eigenbasis
    {k V ι : Type*} [Field k] [AddCommGroup V] [Module k V] [Fintype ι]
    (b : Module.Basis ι k V) (f : Module.End k V) (eigenvalue : ι → k)
    (hf : ∀ i, f (b i) = eigenvalue i • b i) : f.IsSemisimple := by
  let s := Finset.univ.image eigenvalue
  let p : Polynomial k := ∏ a ∈ s, (Polynomial.X - Polynomial.C a)
  have hp : p.Separable := Polynomial.separable_prod_X_sub_C_iff'.mpr (by
    intro x _ y _ h
    exact h)
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp.squarefree
  apply b.ext
  intro i
  rw [Module.End.aeval_apply_of_mem_apply_eq_smul (hf i)]
  have hi : eigenvalue i ∈ s := Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hpi : p.eval (eigenvalue i) = 0 := by
    simp only [p, Polynomial.eval_prod]
    apply Finset.prod_eq_zero hi
    simp
  simp only [hpi, zero_smul, LinearMap.zero_apply]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.EigenbasisSemisimple.Construction
