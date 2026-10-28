import OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.ConeEq
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! # Linear Polynomial -/

namespace OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearPolynomial.Constructions.Cone

noncomputable section

/-!
# Linear functionals and homogeneous polynomial substitution
-/

open Set _root_.MvPolynomial

theorem exists_linear_functional_separating_finite_set
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    {S : Set E} (hS : S.Finite) {x : E} (hx : x ∉ S) :
    ∃ ℓ : E →L[ℂ] ℂ, ∀ y ∈ S, ℓ x ≠ ℓ y := by
  let : Finite S := hS.to_subtype
  obtain ⟨ℓ, hℓ⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ)
    (fun y : S => x - y.val) (fun y => sub_ne_zero.mpr (fun h => hx (h ▸ y.property)))
  refine ⟨ℓ.toContinuousLinearMap, ?_⟩
  intro y hy hxy
  apply hℓ ⟨y, hy⟩
  change ℓ (x - y) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

def linearPolynomial {ι : Type*} [Fintype ι] (ℓ : (ι → ℂ) →L[ℂ] ℂ) : MvPolynomial ι ℂ := by
  classical
  exact ∑ i : ι, C (ℓ (Pi.single i 1)) * X i

theorem linearPolynomial_isHomogeneous {ι : Type*} [Fintype ι]
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) : (linearPolynomial ℓ).IsHomogeneous 1 := by
  exact IsHomogeneous.sum Finset.univ _ 1 (fun i _ => isHomogeneous_C_mul_X _ i)

theorem eval_linearPolynomial {ι : Type*} [Fintype ι]
    (ℓ : (ι → ℂ) →L[ℂ] ℂ) (x : ι → ℂ) : eval x (linearPolynomial ℓ) = ℓ x := by
  classical
  have hx : (∑ i : ι, x i • Pi.single i (1 : ℂ)) = x := by
    ext j
    simp [Pi.smul_apply, Pi.single_apply]
  calc
    _ = ∑ i : ι, ℓ (Pi.single i 1) * x i := by
      simp only [linearPolynomial, map_sum, map_mul, eval_C, eval_X]
    _ = ∑ i : ι, ℓ (x i • Pi.single i 1) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [map_smul, smul_eq_mul, mul_comm]
    _ = ℓ (∑ i : ι, x i • Pi.single i 1) := (map_sum ℓ _ _).symm
    _ = ℓ x := congrArg ℓ hx

theorem exists_homogeneous_linear_substitution
    {ι κ : Type*} [Fintype ι]
    (L : (ι → ℂ) →L[ℂ] (κ → ℂ)) {P : MvPolynomial κ ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) :
    ∃ Q : MvPolynomial ι ℂ, Q.IsHomogeneous d ∧ ∀ x, eval x Q = eval (L x) P := by
  let f : κ → MvPolynomial ι ℂ := fun j =>
    linearPolynomial ((ContinuousLinearMap.proj j).comp L)
  refine ⟨eval₂ C f P, ?_, ?_⟩
  · simpa only [one_mul] using hP.eval₂ C f (fun r => isHomogeneous_C ι r)
      (fun j => linearPolynomial_isHomogeneous _)
  · intro x
    rw [eval_eval₂]
    have hC : (eval x).comp C = RingHom.id ℂ := by ext r; simp
    rw [hC, eval₂_id]
    have hfx : (fun j => eval x (f j)) = L x := by
      funext j
      exact eval_linearPolynomial _ x
    rw [hfx]

end

end OAI.AlgebraicGeometry.ComplexGroups.HolomorphicAlgebraicity.LinearPolynomial.Constructions.Cone
