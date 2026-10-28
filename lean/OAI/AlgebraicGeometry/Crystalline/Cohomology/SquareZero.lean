import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.DividedPowers.DPMorphism
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

/-! # Square Zero -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.SquareZero.SquareZeroDividedPowers

noncomputable section

/-!
# Divided powers on a square-zero extension

The ideal `I ⊕ M` in `A ⊕ M` has divided powers
`γₙ(x,m) = (γₙ(x), γₙ₋₁(x) • m)` for positive `n`.
These operations will extend derivations across relative PD envelopes.
-/

open TrivSqZeroExt

variable {A M : Type*} [CommRing A] [AddCommGroup M]
  [Module A M] [Module Aᵐᵒᵖ M] [IsCentralScalar A M]
  (I : Ideal A) (δ : DividedPowers I)

/-- The inverse image of the PD ideal under the square-zero projection. -/
def ideal : Ideal (TrivSqZeroExt A M) :=
  I.comap (fstHom A A M).toRingHom

@[simp] theorem mem_ideal (x : TrivSqZeroExt A M) :
    x ∈ ideal (M := M) I ↔ x.fst ∈ I := Iff.rfl

variable {I}

/-- The formula before extension by zero away from the ideal. -/
def operation : ℕ → TrivSqZeroExt A M → TrivSqZeroExt A M
  | 0, x => (δ.dpow 0 x.fst, 0)
  | n + 1, x => (δ.dpow (n + 1) x.fst, δ.dpow n x.fst • x.snd)

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
@[simp] theorem operation_fst (n : ℕ) (x : TrivSqZeroExt A M) :
    (operation δ n x).fst = δ.dpow n x.fst := by cases n <;> rfl

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
@[simp] theorem operation_snd_zero (x : TrivSqZeroExt A M) :
    (operation δ 0 x).snd = 0 := rfl

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
@[simp] theorem operation_snd_succ (n : ℕ) (x : TrivSqZeroExt A M) :
    (operation δ (n + 1) x).snd = δ.dpow n x.fst • x.snd := rfl

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
theorem operation_zero {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    operation δ 0 x = 1 := by
  apply TrivSqZeroExt.ext
  · exact δ.dpow_zero hx
  · rfl

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
theorem operation_one {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    operation δ 1 x = x := by
  apply TrivSqZeroExt.ext
  · exact δ.dpow_one hx
  · simp [δ.dpow_zero hx]

theorem operation_add (n : ℕ) {x y : TrivSqZeroExt A M}
    (hx : x.fst ∈ I) (hy : y.fst ∈ I) :
    operation δ n (x + y) =
      ∑ k ∈ Finset.antidiagonal n, operation δ k.1 x * operation δ k.2 y := by
  apply TrivSqZeroExt.ext
  · simpa only [operation_fst, fst_add, fst_sum, fst_mul] using δ.dpow_add hx hy
  · cases n with
    | zero => simp
    | succ n =>
      simp only [operation_snd_succ, fst_add, snd_add, snd_sum, snd_mul,
        operation_fst, op_smul_eq_smul, Finset.sum_add_distrib]
      rw [Finset.Nat.sum_antidiagonal_succ', Finset.Nat.sum_antidiagonal_succ]
      simp only [operation_snd_zero, smul_zero, zero_add, operation_snd_succ,
        smul_smul]
      rw [δ.dpow_add hx hy, smul_add, Finset.sum_smul, Finset.sum_smul, add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_comm]

theorem mul_predecessor {x : A} (hx : x ∈ I) (n : ℕ) :
    x * δ.dpow n x = (n + 1 : ℕ) * δ.dpow (n + 1) x := by
  have h := δ.mul_dpow (m := 1) (n := n) hx
  simpa only [δ.dpow_one hx, Nat.one_add, Nat.choose_one_right] using h

theorem operation_mul (n : ℕ) (a : TrivSqZeroExt A M)
    {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    operation δ n (a * x) = a ^ n * operation δ n x := by
  apply TrivSqZeroExt.ext
  · simp only [operation_fst, fst_mul, fst_pow, δ.dpow_mul hx]
  · cases n with
    | zero => simp
    | succ n =>
      simp only [operation_snd_succ, fst_mul, snd_mul, fst_pow, operation_fst,
        snd_pow, Nat.pred_succ, op_smul_eq_smul, δ.dpow_mul hx, smul_add,
        smul_smul]
      simp only [← Nat.cast_smul_eq_nsmul A, smul_smul]
      congr 1
      · congr 1
        ring
      · congr 1
        calc
          (a.fst ^ n * δ.dpow n x.fst) * x.fst =
              a.fst ^ n * (x.fst * δ.dpow n x.fst) := by ring
          _ = a.fst ^ n * ((n + 1 : ℕ) * δ.dpow (n + 1) x.fst) :=
            congrArg (a.fst ^ n * ·) (mul_predecessor δ hx n)
          _ = _ := by ring

theorem operation_mul_same (m n : ℕ) {x : TrivSqZeroExt A M}
    (hx : x.fst ∈ I) :
    operation δ m x * operation δ n x =
      (Nat.choose (m + n) m : TrivSqZeroExt A M) * operation δ (m + n) x := by
  apply TrivSqZeroExt.ext
  · simp only [fst_mul, operation_fst, fst_natCast, δ.mul_dpow hx]
  · cases m with
    | zero => simp [δ.dpow_zero hx]
    | succ m =>
      cases n with
      | zero => simp [δ.dpow_zero hx]
      | succ n =>
        have hmn : m + 1 + (n + 1) = (m + n + 1) + 1 := by omega
        rw [hmn]
        simp only [snd_mul, operation_fst, operation_snd_succ, op_smul_eq_smul,
          fst_natCast, snd_natCast, smul_zero, add_zero, smul_smul]
        rw [← add_smul, δ.mul_dpow hx, δ.mul_dpow hx]
        congr 1
        rw [Nat.choose_succ_succ, Nat.cast_add, add_mul]
        have h₁ : m + 1 + n = m + n + 1 := by omega
        have h₂ : n + 1 + m = m + n + 1 := by omega
        rw [h₁, Nat.choose_symm_add (a := n + 1) (b := m), h₂]
        simp only [Nat.add_assoc, add_comm]

theorem composition_coefficient {x : A} (hx : x ∈ I) (m n : ℕ) :
    δ.dpow m (δ.dpow (n + 1) x) * δ.dpow n x =
      (Nat.uniformBell (m + 1) (n + 1) : A) * δ.dpow (m * (n + 1) + n) x := by
  rw [δ.dpow_comp (Nat.succ_ne_zero n) hx, mul_assoc, δ.mul_dpow hx,
    Nat.choose_symm_add, Nat.uniformBell_succ_left]
  have h : m * (n + 1) + (n + 1) - 1 = m * (n + 1) + n := by omega
  simp only [h, Nat.add_sub_cancel, Nat.cast_mul]
  ring

omit [IsCentralScalar A M] in
theorem operation_comp (m : ℕ) {n : ℕ} (hn : n ≠ 0)
    {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    operation δ m (operation δ n x) =
      (Nat.uniformBell m n : TrivSqZeroExt A M) * operation δ (m * n) x := by
  apply TrivSqZeroExt.ext
  · simp only [operation_fst, fst_mul, fst_natCast, δ.dpow_comp hn hx]
  · cases m with
    | zero => simp
    | succ m =>
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      have h : (m + 1) * (n + 1) = (m * (n + 1) + n) + 1 := by ring
      rw [h]
      simp only [operation_snd_succ, operation_fst, smul_smul, snd_mul,
        fst_natCast, snd_natCast, smul_zero, add_zero]
      rw [composition_coefficient δ hx]

open scoped Classical in
/-- The divided-power function, extended by zero off the ideal. -/
def dpow (n : ℕ) (x : TrivSqZeroExt A M) : TrivSqZeroExt A M :=
  if x.fst ∈ I then operation δ n x else 0

omit [Module Aᵐᵒᵖ M] [IsCentralScalar A M] in
theorem dpow_of_mem (n : ℕ) {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    SquareZeroDividedPowers.dpow δ n x = operation δ n x := by simp [SquareZeroDividedPowers.dpow, hx]

/-- Divided powers on `I ⊕ M`, with the higher operations zero on `M`. -/
def dividedPowers : DividedPowers (ideal (M := M) I) where
  dpow := SquareZeroDividedPowers.dpow δ
  dpow_null {n x} hx := by
    change x.fst ∉ I at hx
    simp only [SquareZeroDividedPowers.dpow, ite_eq_right hx]
  dpow_zero hx := (dpow_of_mem δ 0 hx).trans (operation_zero δ hx)
  dpow_one hx := (dpow_of_mem δ 1 hx).trans (operation_one δ hx)
  dpow_mem hn hx := by
    rw [dpow_of_mem δ _ hx, mem_ideal, operation_fst]
    exact δ.dpow_mem hn hx
  dpow_add {n x y} hx hy := by
    change x.fst ∈ I at hx
    change y.fst ∈ I at hy
    simp only [dpow_of_mem δ _ hx, dpow_of_mem δ _ hy,
      dpow_of_mem δ n (x := x + y) (I.add_mem hx hy), operation_add δ _ hx hy]
  dpow_mul {n a x} hx := by
    change x.fst ∈ I at hx
    rw [dpow_of_mem δ _ hx,
      dpow_of_mem δ n (x := a * x) (I.mul_mem_left a.fst hx)]
    exact operation_mul δ n a hx
  mul_dpow hx := by
    simp only [dpow_of_mem δ _ hx, operation_mul_same δ _ _ hx]
  dpow_comp {m n x} hn hx := by
    change x.fst ∈ I at hx
    rw [dpow_of_mem δ _ hx, dpow_of_mem δ _ hx,
      dpow_of_mem δ m (x := operation δ n x)
        (by simpa only [operation_fst] using δ.dpow_mem hn hx)]
    exact operation_comp δ _ hn hx

theorem dividedPowers_fst (n : ℕ) {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    ((dividedPowers δ).dpow n x).fst = δ.dpow n x.fst := by
  change (SquareZeroDividedPowers.dpow δ n x).fst = _
  rw [dpow_of_mem δ n hx, operation_fst]

theorem dividedPowers_snd (n : ℕ) {x : TrivSqZeroExt A M} (hx : x.fst ∈ I) :
    ((dividedPowers δ).dpow (n + 1) x).snd = δ.dpow n x.fst • x.snd := by
  change (SquareZeroDividedPowers.dpow δ (n + 1) x).snd = _
  rw [dpow_of_mem δ _ hx, operation_snd_succ]

theorem inl_isDPMorphism :
    DividedPowers.IsDPMorphism δ (dividedPowers (M := M) δ) (inlHom A M) where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => hx)
  dpow_comp {n} x hx := by
    change SquareZeroDividedPowers.dpow δ n (inl x) = inl (δ.dpow n x)
    rw [dpow_of_mem δ n (x := inl x) hx]
    cases n <;> apply TrivSqZeroExt.ext <;> simp

theorem fst_isDPMorphism :
    DividedPowers.IsDPMorphism (dividedPowers (M := M) δ) δ
      (fstHom A A M).toRingHom where
  ideal_comp := Ideal.map_le_iff_le_comap.mpr (fun _ hx => hx)
  dpow_comp _x hx := (dividedPowers_fst δ _ hx).symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.SquareZero.SquareZeroDividedPowers
