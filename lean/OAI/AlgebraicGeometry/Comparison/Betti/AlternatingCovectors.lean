import OAI.AlgebraicGeometry.Comparison.Betti.Smooth.Wedge

/-! # Alternating Covectors -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth

noncomputable section

/-! Alternating-product formulas for iterated genuine one-covectors. -/

open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def covectorTensorValue {n : ℕ} (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (v : Fin n → E) : ℂ :=
  ∏ i, a i (fun _ => v i)

def iteratedCovectorWedge : (n : ℕ) → ℂ →
    (Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) → E [⋀^Fin n]→L[ℝ] ℂ
  | 0, c, _ => ContinuousAlternatingMap.constOfIsEmpty ℝ E (Fin 0) c
  | n + 1, c, a => AlgebraicTopology.Kunneth.CovectorWedge.Constructions.covectorWedge (iteratedCovectorWedge n c (Fin.init a)) (a (Fin.last n))

theorem tensorValue_block {n : ℕ} (a : Fin (n + 1) → E [⋀^Fin 1]→L[ℝ] ℂ) :
    AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (covectorTensorValue (Fin.init a)) (a (Fin.last n)) = covectorTensorValue a := by
  funext v
  rw [covectorTensorValue, Fin.prod_univ_castSucc]
  unfold AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct covectorTensorValue
  congr 1
  apply congrArg (a (Fin.last n))
  funext i
  have hi : i = 0 := Fin.eq_zero i
  subst i
  rfl

/-- The standard iterated wedge is the unnormalized alternating product of its one-covectors. -/
theorem iteratedCovectorWedge_apply : ∀ (n : ℕ) (c : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (v : Fin n → E),
    Smooth.iteratedCovectorWedge n c a v = c * AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (covectorTensorValue a) v := by
  intro n
  induction n with
  | zero =>
      intro c a v
      have hsign (σ : Equiv.Perm (Fin 0)) : Equiv.Perm.sign σ = 1 := by
        rw [show σ = Equiv.refl _ from Subsingleton.elim _ _]
        exact Equiv.Perm.sign_refl
      simp [Smooth.iteratedCovectorWedge, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum, covectorTensorValue, hsign]
  | succ n ih =>
      intro c a v
      rw [Smooth.iteratedCovectorWedge, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.covectorWedge_eq_alternatingSum]
      have hfun : AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (Smooth.iteratedCovectorWedge n c (Fin.init a)) (a (Fin.last n)) =
          fun w => c * AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct (AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (covectorTensorValue (Fin.init a)))
            (a (Fin.last n)) w := by
        funext w
        unfold AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.finBlockProduct
        rw [ih]
        ring
      rw [hfun, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_smul, AlgebraicTopology.Kunneth.FinAlternatingProduct.Constructions.alternatingSum_finBlock_left, tensorValue_block]
      simp only [Nat.factorial_one, Nat.cast_one, mul_one, Complex.real_smul,
        Complex.ofReal_inv, Complex.ofReal_natCast, nsmul_eq_mul]
      have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
      field_simp

theorem tensorValue_swap_invariant {n : ℕ} (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ)
    (i j : Fin n) (h : a i = a j) (v : Fin n → E) :
    covectorTensorValue a (v ∘ Equiv.swap i j) = covectorTensorValue a v := by
  classical
  have ha (k : Fin n) : a (Equiv.swap i j k) = a k := by
    by_cases hi : k = i
    · subst k; simpa using h.symm
    by_cases hj : k = j
    · subst k; simpa using h
    rw [Equiv.swap_apply_of_ne_of_ne hi hj]
  calc
    _ = ∏ k, a (Equiv.swap i j k) (fun _ => v (Equiv.swap i j k)) := by
      simp only [covectorTensorValue, Function.comp_apply, ha]
    _ = _ := Equiv.prod_comp (Equiv.swap i j) (fun k => a k (fun _ => v k))

/-- A repeated one-covector makes the actual iterated exterior product vanish. -/
theorem iteratedCovectorWedge_repeated {n : ℕ} (c : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (i j : Fin n) (hij : i ≠ j) (ha : a i = a j) :
    Smooth.iteratedCovectorWedge n c a = 0 := by
  ext v
  rw [iteratedCovectorWedge_apply]
  have hfun : (fun w => covectorTensorValue a (w ∘ Equiv.swap i j)) = covectorTensorValue a :=
    funext (tensorValue_swap_invariant a i j ha)
  have h := AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_permute (covectorTensorValue a) (Equiv.swap i j) v
  rw [hfun, Equiv.Perm.sign_swap hij] at h
  change AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (covectorTensorValue a) v =
    (-1 : ℤ) • AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (covectorTensorValue a) v at h
  rw [neg_one_zsmul] at h
  have hz : AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum (covectorTensorValue a) v = 0 := (CharZero.eq_neg_self_iff).mp h
  rw [hz, mul_zero]
  rfl

theorem tensorValue_update {n : ℕ} (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ)
    (i : Fin n) (b : E [⋀^Fin 1]→L[ℝ] ℂ) (v : Fin n → E) :
    covectorTensorValue (Function.update a i b) v =
      b (fun _ => v i) * ∏ j ∈ Finset.univ.erase i, a j (fun _ => v j) := by
  classical
  have hfun : (fun j => Function.update a i b j (fun _ => v j)) =
      Function.update (fun j => a j (fun _ => v j)) i (b (fun _ => v i)) := by
    funext j
    by_cases h : j = i
    · subst j; simp
    · simp [h]
  unfold covectorTensorValue
  rw [hfun, Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase]

theorem iteratedCovectorWedge_add_coeff {n : ℕ} (c d : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) :
    Smooth.iteratedCovectorWedge n (c + d) a = Smooth.iteratedCovectorWedge n c a + Smooth.iteratedCovectorWedge n d a := by
  ext v
  change Smooth.iteratedCovectorWedge n (c + d) a v =
    Smooth.iteratedCovectorWedge n c a v + Smooth.iteratedCovectorWedge n d a v
  simp only [iteratedCovectorWedge_apply, add_mul]

theorem iteratedCovectorWedge_smul_coeff {n : ℕ} (c d : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) :
    Smooth.iteratedCovectorWedge n (c * d) a = c • Smooth.iteratedCovectorWedge n d a := by
  ext v
  change Smooth.iteratedCovectorWedge n (c * d) a v = c * Smooth.iteratedCovectorWedge n d a v
  simp only [iteratedCovectorWedge_apply, mul_assoc]

theorem iteratedCovectorWedge_add_slot {n : ℕ} (c : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (i : Fin n) (b d : E [⋀^Fin 1]→L[ℝ] ℂ) :
    Smooth.iteratedCovectorWedge n c (Function.update a i (b + d)) =
      Smooth.iteratedCovectorWedge n c (Function.update a i b) +
        Smooth.iteratedCovectorWedge n c (Function.update a i d) := by
  ext v
  change Smooth.iteratedCovectorWedge n c (Function.update a i (b + d)) v =
    Smooth.iteratedCovectorWedge n c (Function.update a i b) v +
      Smooth.iteratedCovectorWedge n c (Function.update a i d) v
  simp only [iteratedCovectorWedge_apply]
  have hfun : covectorTensorValue (Function.update a i (b + d)) =
      fun w => covectorTensorValue (Function.update a i b) w +
        covectorTensorValue (Function.update a i d) w := by
    funext w
    simp only [tensorValue_update]
    change (b (fun _ => w i) + d (fun _ => w i)) * _ = _
    exact add_mul _ _ _
  rw [hfun, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_add, mul_add]

theorem iteratedCovectorWedge_smul_slot {n : ℕ} (c r : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (i : Fin n) (b : E [⋀^Fin 1]→L[ℝ] ℂ) :
    Smooth.iteratedCovectorWedge n c (Function.update a i (r • b)) =
      r • Smooth.iteratedCovectorWedge n c (Function.update a i b) := by
  ext v
  change Smooth.iteratedCovectorWedge n c (Function.update a i (r • b)) v =
    r * Smooth.iteratedCovectorWedge n c (Function.update a i b) v
  simp only [iteratedCovectorWedge_apply]
  have hfun : covectorTensorValue (Function.update a i (r • b)) =
      fun w => r * covectorTensorValue (Function.update a i b) w := by
    funext w
    simp only [tensorValue_update]
    change (r * b (fun _ => w i)) * _ = r * (b (fun _ => w i) * _)
    exact mul_assoc _ _ _
  rw [hfun, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_smul, mul_left_comm c r]

theorem iteratedCovectorWedge_zero_slot {n : ℕ} (c : ℂ)
    (a : Fin n → E [⋀^Fin 1]→L[ℝ] ℂ) (i : Fin n) :
    Smooth.iteratedCovectorWedge n c (Function.update a i 0) = 0 := by
  ext v
  rw [iteratedCovectorWedge_apply]
  have hfun : covectorTensorValue (Function.update a i 0) = fun _ => 0 := by
    funext w
    rw [tensorValue_update]
    exact zero_mul _
  rw [hfun, AlgebraicTopology.Kunneth.WedgeAlternating.Constructions.alternatingSum_zero, mul_zero]
  rfl

end

end OAI.AlgebraicGeometry.Comparison.Betti.AlternatingCovectors.Smooth
