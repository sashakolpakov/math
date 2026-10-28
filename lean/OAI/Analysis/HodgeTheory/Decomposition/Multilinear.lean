import OAI.Analysis.HodgeTheory.Decomposition.Types
import Mathlib.LinearAlgebra.Multilinear.FiniteDimensional
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Multilinear -/

namespace OAI.Analysis.HodgeTheory.Decomposition.Multilinear.Constructions

noncomputable section

/-! The genuine real multilinear covectors split into complex and conjugate
linear characters in each slot. This is the pointwise algebra for type projections. -/

open scoped BigOperators

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℂ E]
  [IsScalarTower ℝ ℂ E]

abbrev RealMultilinear (n : ℕ) := MultilinearMap ℝ (fun _ : Fin n => E) ℂ

/-- Insert the genuine complex structure into one argument. -/
def slotRotation (n : ℕ) (i : Fin n) : Module.End ℂ (RealMultilinear E n) where
  toFun f := f.compLinearMap (fun j => if j = i then
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).toLinearMap else LinearMap.id)
  map_add' f g := by ext v; rfl
  map_smul' c f := by ext v; rfl

@[simp]
theorem slotRotation_apply (n : ℕ) (i : Fin n) (f : RealMultilinear E n) (v : Fin n → E) :
    slotRotation E n i f v = f (Function.update v i (Complex.I • v i)) := by
  change f (fun j => (if j = i then
    (ContinuousLinearMap.lsmul ℝ ℂ Complex.I).toLinearMap else LinearMap.id) (v j)) = _
  congr 1
  funext j
  by_cases hj : j = i <;> simp [hj]

theorem slotRotation_square (n : ℕ) (i : Fin n) :
    slotRotation E n i * slotRotation E n i = -1 := by
  ext f v
  change slotRotation E n i (slotRotation E n i f) v = -f v
  rw [slotRotation_apply, slotRotation_apply, Function.update_self,
    smul_smul, Complex.I_mul_I, neg_one_smul, Function.update_idem,
    f.map_update_neg, Function.update_eq_self]

theorem slotRotation_commute (n : ℕ) (i j : Fin n) :
    Commute (slotRotation E n i) (slotRotation E n j) := by
  by_cases hij : i = j
  · subst j
    rfl
  · ext f v
    change slotRotation E n i (slotRotation E n j f) v =
      slotRotation E n j (slotRotation E n i f) v
    simp only [slotRotation_apply, Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    rw [Function.update_comm hij]

section Quadratic

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem square_neg_one_semisimple (T : Module.End ℂ V) (hT : T * T = -1) :
    T.IsSemisimple := by
  have hp := (Polynomial.separable_X_pow_sub_C (-1 : ℂ)
    (n := 2) (by norm_num) (by norm_num)).squarefree
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hp
  simp only [pow_two, map_sub, map_mul, Polynomial.aeval_X,
    map_neg, map_one, hT, sub_self]

theorem square_neg_one_eigenvalues (T : Module.End ℂ V) (hT : T * T = -1)
    (μ : ℂ) (f : V) (hf : f ≠ 0) (hμ : T f = μ • f) :
    μ = Complex.I ∨ μ = -Complex.I := by
  have hh := LinearMap.congr_fun hT f
  change T (T f) = -f at hh
  rw [hμ, map_smul, hμ, smul_smul] at hh
  have he : (μ * μ + 1) • f = 0 := by
    rw [add_smul, one_smul, hh, neg_add_cancel]
  have hz : μ * μ + 1 = 0 := (smul_eq_zero.mp he).resolve_right hf
  have hfactor : (μ - Complex.I) * (μ + Complex.I) = 0 := by
    calc
      (μ - Complex.I) * (μ + Complex.I) = μ * μ - Complex.I * Complex.I := by ring
      _ = 0 := by rw [Complex.I_mul_I]; simpa using hz
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

end Quadratic

/-- The two actual slot eigenvalues define each signed subspace. -/
def signedMultilinearSpace (n : ℕ) (ε : Fin n → Bool) : Submodule ℂ (RealMultilinear E n) :=
  ⨅ i, (slotRotation E n i).eigenspace (if ε i then Complex.I else -Complex.I)

variable [FiniteDimensional ℝ E]

instance realMultilinear_finiteDimensional (n : ℕ) : FiniteDimensional ℂ (RealMultilinear E n) :=
  Module.Finite.of_restrictScalars_finite ℝ ℂ (RealMultilinear E n)

theorem multilinear_joint_eigenspaces_span (n : ℕ) :
    (⨆ χ : Fin n → ℂ, ⨅ i, (slotRotation E n i).eigenspace (χ i)) = ⊤ := by
  have hs (i : Fin n) := (square_neg_one_semisimple (slotRotation E n i)
    (slotRotation_square E n i)).isFinitelySemisimple
  have h := Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (slotRotation E n) (fun i j _ => slotRotation_commute E n i j)
    (fun i => Module.End.iSup_maxGenEigenspace_eq_top (slotRotation E n i))
  simpa only [fun i μ => (hs i).maxGenEigenspace_eq_eigenspace μ] using h

/-- All real multilinear covectors are sums of the signed complex-linear pieces. -/
theorem signedMultilinearSpace_span (n : ℕ) :
    (⨆ ε : Fin n → Bool, signedMultilinearSpace E n ε) = ⊤ := by
  classical
  apply top_unique
  rw [← multilinear_joint_eigenspaces_span E n]
  refine iSup_le fun χ => ?_
  intro f hf
  by_cases hzero : f = 0
  · subst f
    exact Submodule.zero_mem _
  let ε : Fin n → Bool := fun i => decide (χ i = Complex.I)
  apply le_iSup (signedMultilinearSpace E n) ε
  simp only [signedMultilinearSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  intro i
  have hi := (iInf_le (fun j => (slotRotation E n j).eigenspace (χ j)) i) hf
  rw [Module.End.mem_eigenspace_iff] at hi
  rcases square_neg_one_eigenvalues (slotRotation E n i) (slotRotation_square E n i)
    (χ i) f hzero hi with h | h
  · simpa [ε, h] using hi
  · have hne : χ i ≠ Complex.I := by
      rw [h]
      intro he
      have him := congrArg Complex.im he
      norm_num at him
    have heps : ε i = false := by simp [ε, hne]
    simpa only [heps, Bool.false_eq_true, ite_false, h] using hi

end

end OAI.Analysis.HodgeTheory.Decomposition.Multilinear.Constructions
