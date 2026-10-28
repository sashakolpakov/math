import Mathlib

/-! # Multilinear Basis Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearBasisCoordinates.Construction

noncomputable section

/-! Multilinear forms are determined by finitely many basis evaluations.
Their values on arbitrary inputs have a finite polynomial expansion in
the input coordinates. -/

open scoped Classical

def multilinearBasisEvaluation
    {R E A I : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] (b : Module.Basis I R E) (r : ℕ) :
    MultilinearMap R (fun _ : Fin r => E) A →ₗ[R] ((Fin r → I) → A) where
  toFun f t := f (fun i => b (t i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem multilinearBasisEvaluation_injective
    {R E A I : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] (b : Module.Basis I R E) (r : ℕ) :
    Function.Injective (multilinearBasisEvaluation (A := A) b r) := by
  intro f g he
  exact Module.Basis.ext_multilinear (fun _ : Fin r => b) (fun t => congrFun he t)

def multilinearBasisEvaluationEquiv
    {R E A I : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] (b : Module.Basis I R E) (r : ℕ) :
    MultilinearMap R (fun _ : Fin r => E) A ≃ₗ[R] (multilinearBasisEvaluation (A := A) b r).range :=
  LinearEquiv.ofInjective _ (multilinearBasisEvaluation_injective b r)

theorem multilinear_basis_expansion
    {R E A I : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A] [Fintype I] (b : Module.Basis I R E) (r : ℕ)
    (f : MultilinearMap R (fun _ : Fin r => E) A) (v : Fin r → E) :
    f v = ∑ t : Fin r → I, (∏ i, b.repr (v i) (t i)) • f (fun i => b (t i)) := by
  have hv : v = fun i => ∑ j, b.repr (v i) j • b j := by
    funext i
    exact (b.sum_repr (v i)).symm
  conv_lhs => rw [hv]
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro t _
  exact f.map_smul_univ _ _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MultilinearBasisCoordinates.Construction
