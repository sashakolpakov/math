import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! Algebra behind exhaustive maximal-nonzero-minor row selection.
Only original rows are selected; inverses occur solely in the correctness proof. -/

namespace SubexponentialSAT.SqrtLog.RowSelection

open scoped BigOperators Matrix

variable {a b s : ℕ}

/-- Restriction of an integer matrix to an ordered square pair of index tuples. -/
def minor (P : Fin a → Fin b → ℤ) (rows : Fin s → Fin a)
    (cols : Fin s → Fin b) : Matrix (Fin s) (Fin s) ℤ :=
  fun i j => P (rows i) (cols j)

/-- The corresponding rational matrix, used only in algebraic certificates. -/
def qmatrix (P : Fin a → Fin b → ℤ) : Matrix (Fin a) (Fin b) ℚ :=
  fun i j => (P i j : ℚ)

theorem det_cast (P : Fin a → Fin b → ℤ) (rows : Fin s → Fin a)
    (cols : Fin s → Fin b) :
    ((minor P rows cols).det : ℚ) =
      ((qmatrix P).submatrix rows cols).det := by
  exact (Int.castRingHom ℚ).map_det (minor P rows cols)

theorem independent_of_minor (P : Fin a → Fin b → ℤ)
    (rows : Fin s → Fin a) (cols : Fin s → Fin b)
    (h : (minor P rows cols).det ≠ 0) :
    LinearIndependent ℚ (fun i => qmatrix P (rows i)) := by
  have hq : ((qmatrix P).submatrix rows cols).det ≠ 0 := by
    rw [← det_cast]
    exact_mod_cast h
  let project : (Fin b → ℚ) →ₗ[ℚ] (Fin s → ℚ) :=
    LinearMap.pi fun i => LinearMap.proj (cols i)
  exact LinearIndependent.of_comp project
    (Matrix.linearIndependent_rows_of_det_ne_zero hq)

theorem rows_injective_of_minor (P : Fin a → Fin b → ℤ)
    (rows : Fin s → Fin a) (cols : Fin s → Fin b)
    (h : (minor P rows cols).det ≠ 0) : Function.Injective rows := by
  intro i j hij
  apply (independent_of_minor P rows cols h).injective
  simp only [hij]

theorem cols_injective_of_minor (P : Fin a → Fin b → ℤ)
    (rows : Fin s → Fin a) (cols : Fin s → Fin b)
    (h : (minor P rows cols).det ≠ 0) : Function.Injective cols := by
  apply rows_injective_of_minor (fun j i => P i j) cols rows
  change (minor P rows cols).transpose.det ≠ 0
  simpa only [Matrix.det_transpose] using h

theorem selected_span_le (P : Fin a → Fin b → ℤ) (rows : Fin s → Fin a) :
    Submodule.span ℚ (Set.range (fun i => qmatrix P (rows i))) ≤
      Submodule.span ℚ (Set.range (qmatrix P)) := by
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨rows i, rfl⟩

theorem span_eq_of_rank_le_size (P : Fin a → Fin b → ℤ)
    (rows : Fin s → Fin a) (cols : Fin s → Fin b)
    (h : (minor P rows cols).det ≠ 0)
    (hrank : Module.finrank ℚ (Submodule.span ℚ (Set.range (qmatrix P))) ≤ s) :
    Submodule.span ℚ (Set.range (fun i => qmatrix P (rows i))) =
      Submodule.span ℚ (Set.range (qmatrix P)) := by
  apply Submodule.eq_of_le_of_finrank_le (selected_span_le P rows)
  simpa only [finrank_span_eq_card (independent_of_minor P rows cols h),
    Fintype.card_fin] using hrank

/-- Append a row or column index using the canonical sum-index equivalence. -/
def appendIndex {d : ℕ} (u : Fin s → Fin d) (x : Fin d) : Fin (s + 1) → Fin d :=
  Sum.elim u (fun _ : Fin 1 => x) ∘ (finSumFinEquiv : Fin s ⊕ Fin 1 ≃ Fin (s+1)).symm

/-- Zero determinants of all one-row/one-column borders force rational spanning. -/
theorem span_eq_of_borders_zero (P : Fin a → Fin b → ℤ)
    (rows : Fin s → Fin a) (cols : Fin s → Fin b)
    (h : (minor P rows cols).det ≠ 0)
    (hb : ∀ i j, (minor P (appendIndex rows i) (appendIndex cols j)).det = 0) :
    Submodule.span ℚ (Set.range (fun i => qmatrix P (rows i))) =
      Submodule.span ℚ (Set.range (qmatrix P)) := by
  classical
  let A := (qmatrix P).submatrix rows cols
  have hA : A.det ≠ 0 := by
    change ((qmatrix P).submatrix rows cols).det ≠ 0
    rw [← det_cast]
    exact_mod_cast h
  let _ : Invertible A := ((Matrix.isUnit_iff_isUnit_det A).mpr
    (isUnit_iff_ne_zero.mpr hA)).invertible
  apply le_antisymm (selected_span_le P rows)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  let c : Fin s → ℚ := fun k => ∑ l, qmatrix P i (cols l) * (⅟ A) l k
  apply (Submodule.mem_span_range_iff_exists_fun ℚ).mpr
  refine ⟨c, ?_⟩
  funext j
  let B : Matrix (Fin s) (Fin 1) ℚ := fun k _ => qmatrix P (rows k) j
  let C : Matrix (Fin 1) (Fin s) ℚ := fun _ l => qmatrix P i (cols l)
  let D : Matrix (Fin 1) (Fin 1) ℚ := fun _ _ => qmatrix P i j
  have hblock : (Matrix.fromBlocks A B C D).det = 0 := by
    have hx := congrArg (fun z : ℤ => (z : ℚ)) (hb i j)
    change ((minor P (appendIndex rows i) (appendIndex cols j)).det : ℚ) = 0 at hx
    rw [det_cast] at hx
    have heq : (qmatrix P).submatrix (appendIndex rows i) (appendIndex cols j) =
        (Matrix.fromBlocks A B C D).submatrix
          (finSumFinEquiv : Fin s ⊕ Fin 1 ≃ Fin (s+1)).symm
          (finSumFinEquiv : Fin s ⊕ Fin 1 ≃ Fin (s+1)).symm := by
      ext k l
      simp only [Matrix.submatrix_apply, appendIndex, Function.comp_apply]
      generalize (finSumFinEquiv.symm k) = k'
      generalize (finSumFinEquiv.symm l) = l'
      cases k' <;> cases l' <;> rfl
    rw [heq, Matrix.det_submatrix_equiv_self] at hx
    exact hx
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_unique (D - C * ⅟ A * B)] at hblock
  have hz := (mul_eq_zero.mp hblock).resolve_left hA
  have hz' : qmatrix P i j = ∑ k, c k * qmatrix P (rows k) j := by
    apply sub_eq_zero.mp
    change qmatrix P i j -
      ∑ k, (∑ l, qmatrix P i (cols l) * (⅟ A) l k) * qmatrix P (rows k) j = 0
    change qmatrix P i j -
      ∑ k, (∑ l, qmatrix P i (cols l) * (⅟ A) l k) * qmatrix P (rows k) j = 0 at hz
    exact hz
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hz'.symm

end SubexponentialSAT.SqrtLog.RowSelection

end OAI.Algorithms
