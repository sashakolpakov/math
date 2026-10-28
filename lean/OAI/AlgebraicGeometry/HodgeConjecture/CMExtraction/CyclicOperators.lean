import Mathlib

/-! # Cyclic Operators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CyclicOperators.Radial

noncomputable section

/-! A commuting operator on a finite cyclic space is a linear
combination of powers of the cyclic operator. -/

open scoped Classical

theorem cyclic_commuting_operator
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D A : Module.End ℂ W) (v : W) (M : ℕ)
    (hspan : Submodule.span ℂ (Set.range (fun i : Fin M => (D ^ i.val) v)) = ⊤)
    (hcomm : Commute A D) :
    ∃ c : Fin M → ℂ, A = ∑ i : Fin M, c i • D ^ i.val := by
  have hv : A v ∈ Submodule.span ℂ (Set.range (fun i : Fin M => (D ^ i.val) v)) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  let P : Module.End ℂ W := ∑ i : Fin M, c i • D ^ i.val
  have hp : P v = A v := by
    simpa only [P, LinearMap.sum_apply, LinearMap.smul_apply] using hc
  have hpcomm : Commute P D := by
    change P * D = D * P
    simp only [P, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun B : Module.End ℂ W => c i • B) ((Commute.self_pow D i.val).eq.symm)
  refine ⟨c, ?_⟩
  apply LinearMap.ext_on_range hspan
  intro i
  calc
    A ((D ^ i.val) v) = (D ^ i.val) (A v) :=
      congrArg (fun B : Module.End ℂ W => B v) (hcomm.pow_right i.val).eq
    _ = (D ^ i.val) (P v) := by rw [hp]
    _ = P ((D ^ i.val) v) :=
      (congrArg (fun B : Module.End ℂ W => B v) (hpcomm.pow_right i.val).eq).symm

theorem end_pow_of_eigenvector
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    (D : Module.End ℂ W) (e : ℂ) (x : W) (hx : D x = e • x) (n : ℕ) :
    (D ^ n) x = e ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, hx, map_smul, ih, smul_smul, pow_succ, mul_comm]

theorem linear_map_pow_relation
    {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (D : Module.End ℂ V) (Θ : V →ₗ[ℂ] W) (e : ℂ)
    (h : ∀ b, Θ (D b) = e • Θ b) (n : ℕ) (b : V) :
    Θ ((D ^ n) b) = e ^ n • Θ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, ih, h, smul_smul, pow_succ]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CyclicOperators.Radial
