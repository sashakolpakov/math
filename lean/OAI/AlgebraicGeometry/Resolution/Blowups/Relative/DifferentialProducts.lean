import OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialBlowup
import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-! # Differential Products -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts.Construction

noncomputable section

/-! Relative differential ideals of sums and products with ideal powers. -/

variable (k : Type*) {R : Type*} [CommRing k] [CommRing R] [Algebra k R]

theorem firstRelativeDifferentialIdeal_iSup {ι : Sort*} (J : ι → Ideal R) :
    DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (⨆ i, J i) =
      ⨆ i, DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J i) := by
  apply le_antisymm
  · apply sup_le
    · exact iSup_mono fun i => DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k (J i)
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, p⟩, rfl⟩
      have hD : (⨆ i, J i).restrictScalars k ≤
          ((⨆ i, DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J i)).restrictScalars k).comap
            D.toLinearMap := by
        rw [Submodule.restrictScalars_iSup]
        apply iSup_le
        intro i x hx
        exact (le_iSup (fun i => DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J i)) i)
          (DifferentialBlowup.Construction.relative_derivation_mem_first k (J i) D hx)
      exact hD p.property
  · apply iSup_le
    intro i
    exact DifferentialBlowup.Construction.firstRelativeDifferentialIdeal_mono k (le_iSup J i)

theorem iteratedRelativeDifferentialIdeal_iSup {ι : Sort*} (J : ι → Ideal R) (n : ℕ) :
    DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (⨆ i, J i) n =
      ⨆ i, DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J i) n := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    simp only [DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal, firstRelativeDifferentialIdeal_iSup]
    exact ih _

theorem firstRelativeDifferentialIdeal_sup (J L : Ideal R) :
    DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J ⊔ L) =
      DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J ⊔ DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k L := by
  apply le_antisymm
  · apply sup_le
    · exact sup_le_sup (DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J)
        (DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k L)
    · apply Ideal.span_le.mpr
      rintro _ ⟨⟨D, p⟩, rfl⟩
      obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp p.property
      change D p.val ∈ DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J ⊔ DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k L
      rw [← hxy, map_add]
      exact Submodule.add_mem_sup (DifferentialBlowup.Construction.relative_derivation_mem_first k J D hx)
        (DifferentialBlowup.Construction.relative_derivation_mem_first k L D hy)
  · exact sup_le (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal_mono k le_sup_left)
      (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal_mono k le_sup_right)

theorem iteratedRelativeDifferentialIdeal_sup (J L : Ideal R) (n : ℕ) :
    DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J ⊔ L) n =
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J n ⊔ DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k L n := by
  induction n generalizing J L with
  | zero => rfl
  | succ n ih =>
    simp only [DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal, firstRelativeDifferentialIdeal_sup]
    exact ih _ _

theorem iteratedRelativeDifferentialIdeal_add (J : Ideal R) (m n : ℕ) :
    DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J (m + n) =
      DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m) n := by
  induction m generalizing J with
  | zero => simp only [Nat.zero_add, DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal]
  | succ m ih =>
    rw [Nat.succ_add]
    exact ih (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J)

theorem firstRelativeDifferentialIdeal_product_power_le (J T : Ideal R) (j : ℕ) :
    DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J * T ^ (j + 1)) ≤
      DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J * T ^ (j + 1) ⊔ J * T ^ j := by
  apply sup_le
  · exact (Ideal.mul_mono (DifferentialBlowup.Construction.le_firstRelativeDifferentialIdeal k J) le_rfl).trans le_sup_left
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨D, p⟩, rfl⟩
    change D p.val ∈ DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J * T ^ (j + 1) ⊔ J * T ^ j
    refine Submodule.mul_induction_on p.property ?_ ?_
    · intro x hx y hy
      rw [D.leibniz]
      change x * D y + y * D x ∈ _
      apply Ideal.add_mem
      · exact Submodule.mem_sup_right (Ideal.mul_mem_mul hx
          (DifferentialOrder.Construction.derivation_mem_pow (D.restrictScalars ℤ) T j hy))
      · rw [mul_comm y (D x)]
        exact Submodule.mem_sup_left (Ideal.mul_mem_mul
          (DifferentialBlowup.Construction.relative_derivation_mem_first k J D hx) hy)
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- An ideal with `m+1` differential orders of vanishing along `T`, multiplied
by `T^j`, gains `j` further differential orders. -/
theorem relativeDifferential_product_power_bound (J T : Ideal R) (m j : ℕ)
    (hJ : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k J m ≤ T) :
    DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k (J * T ^ j) (m + j) ≤ T := by
  induction m generalizing J j with
  | zero =>
    have hprod : J * T ^ j ≤ T ^ (j + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mono hJ le_rfl
    have h := DifferentialIdealTransform.Construction.iteratedDifferentialIdeal_le_pow T (J * T ^ j) 1 j
      (by simpa only [Nat.add_comm 1 j] using hprod)
    have hpow : DifferentialIdealTransform.Construction.iteratedDifferentialIdeal (J * T ^ j) j ≤ T := by
      simpa only [pow_one] using h
    simpa only [Nat.zero_add] using
      (DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_le_ordinary k (J * T ^ j) j).trans hpow
  | succ m ihm =>
    induction j with
    | zero => simpa only [pow_zero, mul_one, Nat.add_zero] using hJ
    | succ j ihj =>
      have hstep := DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal_mono k (m + j + 1)
        (firstRelativeDifferentialIdeal_product_power_le k J T j)
      rw [iteratedRelativeDifferentialIdeal_sup] at hstep
      have hleft := ihm (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k J) (j + 1) hJ
      have hright := ihj
      have hbound : DifferentialBlowup.Construction.iteratedRelativeDifferentialIdeal k
          (DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (J * T ^ (j + 1))) (m + j + 1) ≤ T :=
        hstep.trans (sup_le (by simpa only [Nat.add_assoc] using hleft)
          (by simpa only [Nat.succ_add, Nat.add_succ] using hright))
      rw [show m.succ + j.succ = (m + j + 1) + 1 by omega]
      exact hbound

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Relative.DifferentialProducts.Construction
