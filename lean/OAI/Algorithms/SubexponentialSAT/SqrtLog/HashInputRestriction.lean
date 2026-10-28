import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidence

namespace OAI.Algorithms

/-! Substitution of fixed original bits into the actual hash polynomials. -/
namespace SubexponentialSAT.SqrtLog.HashInput

open scoped BigOperators
noncomputable section

variable {V E R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

def restrictionVariable (H : Finset V) (a : H → Bool) (v : V) :
    MvPolynomial {v : V // v ∉ H} R :=
  if hv : v ∈ H then MvPolynomial.C (boolValue (a ⟨v, hv⟩))
  else MvPolynomial.X ⟨v, hv⟩

def restrictPolynomial (H : Finset V) (a : H → Bool) :
    MvPolynomial V R →ₐ[R] MvPolynomial {v : V // v ∉ H} R :=
  MvPolynomial.bind₁ (restrictionVariable H a)

omit [Fintype V] in
@[simp] theorem restrictPolynomial_C (H : Finset V) (a : H → Bool) (r : R) :
    restrictPolynomial H a (MvPolynomial.C r) = MvPolynomial.C r :=
  MvPolynomial.bind₁_C_right _ _

omit [Fintype V] in
@[simp] theorem restrictPolynomial_X (H : Finset V) (a : H → Bool) (v : V) :
    restrictPolynomial (R := R) H a (MvPolynomial.X v) = restrictionVariable H a v :=
  MvPolynomial.bind₁_X_right _ _

omit [Fintype V] in
@[simp] theorem eval_restrictionVariable (H : Finset V) (a : H → Bool)
    (b : {v : V // v ∉ H} → Bool) (v : V) :
    MvPolynomial.eval (fun w => boolValue (R := R) (b w)) (restrictionVariable H a v) =
      boolValue (HighIncidence.glue H a b v) := by
  by_cases hv : v ∈ H <;> simp [restrictionVariable, HighIncidence.glue, hv]

omit [Fintype V] in
theorem eval_restrictPolynomial (H : Finset V) (a : H → Bool)
    (b : {v : V // v ∉ H} → Bool) (p : MvPolynomial V R) :
    MvPolynomial.eval (fun w => boolValue (R := R) (b w)) (restrictPolynomial H a p) =
      MvPolynomial.eval (fun v => boolValue (HighIncidence.glue H a b v)) p := by
  change MvPolynomial.eval _ (MvPolynomial.eval₂ MvPolynomial.C
    (restrictionVariable H a) p) = _
  rw [MvPolynomial.eval₂_comp_left]
  apply MvPolynomial.eval₂Hom_congr
  · ext c
    simp
  · funext v
    exact eval_restrictionVariable H a b v
  · rfl

variable [Nontrivial R]

omit [Fintype V] in
theorem totalDegree_restrictionVariable (H : Finset V) (a : H → Bool) (v : V) :
    (restrictionVariable (R := R) H a v).totalDegree ≤ 1 := by
  unfold restrictionVariable
  split_ifs <;> simp

omit [Fintype V] in
theorem totalDegree_restrict_falsifyingLiteral (H : Finset V) (a : H → Bool)
    (l : SAT.Literal V) :
    (restrictPolynomial H a (falsifyingLiteral (R := R) l)).totalDegree ≤ 1 := by
  unfold falsifyingLiteral
  split_ifs
  · rw [map_sub, map_one, restrictPolynomial_X]
    exact (MvPolynomial.totalDegree_sub _ _).trans
      (max_le (by simp) (totalDegree_restrictionVariable H a l.variable))
  · rw [restrictPolynomial_X]
    exact totalDegree_restrictionVariable H a l.variable

omit [Fintype V] in
theorem totalDegree_restrict_clauseViolation (H : Finset V) (a : H → Bool)
    (C : SAT.Clause V) :
    (restrictPolynomial H a (clauseViolation (R := R) C)).totalDegree ≤ C.card := by
  rw [clauseViolation, map_prod]
  calc
    _ ≤ ∑ l ∈ C, (restrictPolynomial H a (falsifyingLiteral (R := R) l)).totalDegree :=
      MvPolynomial.totalDegree_finsetProd _ _
    _ ≤ ∑ _l ∈ C, 1 := Finset.sum_le_sum fun l _ => totalDegree_restrict_falsifyingLiteral H a l
    _ = _ := by simp

omit [Fintype V] in
theorem vars_restrictPolynomial (H : Finset V) (a : H → Bool)
    (p : MvPolynomial V R) (s : Finset V) (hp : p.vars ⊆ s) :
    (restrictPolynomial H a p).vars ⊆ Finset.subtype (fun v => v ∉ H) s := by
  intro v hv
  obtain ⟨w, hw, hv⟩ := Finset.mem_biUnion.mp (MvPolynomial.vars_bind₁ _ _ hv)
  by_cases wh : w ∈ H
  · simp [restrictionVariable, wh] at hv
  · have heq : v = ⟨w, wh⟩ := by simpa [restrictionVariable, wh] using hv
    subst v
    exact Finset.mem_subtype.mpr (hp hw)

variable [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
omit [Fintype V] in
theorem totalDegree_restrict_hashPolynomial (H : Finset V) (a : H → Bool)
    (C : E → SAT.Clause V) (h : E → R) (k : ℕ)
    (hwidth : ∀ e, (C e).card ≤ k) :
    (restrictPolynomial H a (hashPolynomial C h)).totalDegree ≤ k := by
  rw [hashPolynomial, map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro e _
  rw [map_mul]
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simpa only [restrictPolynomial_C, MvPolynomial.totalDegree_C, zero_add] using
      (totalDegree_restrict_clauseViolation (R := R) H a (C e)).trans (hwidth e))

omit [Fintype V] [DecidableEq E] in
theorem vars_restrict_hashPolynomial (H : Finset V) (a : H → Bool)
    (C : E → SAT.Clause V) (h : E → R) :
    (restrictPolynomial H a (hashPolynomial C h)).vars ⊆
      Finset.subtype (fun v => v ∉ H) (hashScope C h) :=
  vars_restrictPolynomial H a _ _ (vars_hashPolynomial C h)

end
end SubexponentialSAT.SqrtLog.HashInput

end OAI.Algorithms
