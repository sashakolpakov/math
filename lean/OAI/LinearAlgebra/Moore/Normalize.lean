import OAI.LinearAlgebra.Moore.Basic

/-! Normalization of the Pfaffian on a standard symplectic matrix. -/

namespace OAI.LinearAlgebra.Moore

open Matrix

def pairPermutation (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ρ : Fin n → Equiv.Perm (Fin 2)) : Equiv.Perm (Fin n × Fin 2) :=
  Equiv.prodCongrLeft (fun _ : Fin 2 => τ) * Equiv.prodCongrRight ρ

theorem pairPermutation_apply (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ρ : Fin n → Equiv.Perm (Fin 2)) (i : Fin n) (a : Fin 2) :
    pairPermutation n τ ρ (i, a) = (τ i, ρ i a) := by
  rfl

theorem pairPermutation_sign (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ρ : Fin n → Equiv.Perm (Fin 2)) :
    Equiv.Perm.sign (pairPermutation n τ ρ) = ∏ i, Equiv.Perm.sign (ρ i) := by
  rw [pairPermutation, Equiv.Perm.sign_mul, Equiv.Perm.sign_prodCongrLeft,
    Equiv.Perm.sign_prodCongrRight, Fin.prod_univ_two, Int.units_mul_self, one_mul]

theorem pairPermutation_injective (n : ℕ) : Function.Injective
    (fun p : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm (Fin 2)) =>
      pairPermutation n p.1 p.2) := by
  intro ⟨τ, ρ⟩ ⟨τ', ρ'⟩ h
  have ht : τ = τ' := by
    apply Equiv.ext
    intro i
    exact congrArg (fun σ : Equiv.Perm (Fin n × Fin 2) => (σ (i, 0)).1) h
  have hr : ρ = ρ' := by
    funext i
    apply Equiv.ext
    intro a
    exact congrArg (fun σ : Equiv.Perm (Fin n × Fin 2) => (σ (i, a)).2) h
  exact Prod.ext ht hr

def PreservesPairs (n : ℕ) (σ : Equiv.Perm (Fin n × Fin 2)) : Prop :=
  ∀ i : Fin n, (σ (i, 0)).1 = (σ (i, 1)).1

theorem pairPermutation_preserves (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ρ : Fin n → Equiv.Perm (Fin 2)) : PreservesPairs n (pairPermutation n τ ρ) := by
  intro i
  rfl

theorem exists_pairPermutation (n : ℕ) (σ : Equiv.Perm (Fin n × Fin 2))
    (hσ : PreservesPairs n σ) :
    ∃ (τ : Equiv.Perm (Fin n)) (ρ : Fin n → Equiv.Perm (Fin 2)),
      pairPermutation n τ ρ = σ := by
  have hf (i : Fin n) (a : Fin 2) : (σ (i, a)).1 = (σ (i, 0)).1 := by
    fin_cases a
    · rfl
    · exact (hσ i).symm
  have hinj (i : Fin n) : Function.Injective (fun a : Fin 2 => (σ (i, a)).2) := by
    intro a b hab
    have he : σ (i, a) = σ (i, b) := Prod.ext ((hf i a).trans (hf i b).symm) hab
    exact congrArg Prod.snd (σ.injective he)
  let ρ : Fin n → Equiv.Perm (Fin 2) := fun i =>
    Equiv.ofBijective (fun a : Fin 2 => (σ (i, a)).2) ((Finite.injective_iff_bijective).mp (hinj i))
  have hτ : Function.Injective (fun i : Fin n => (σ (i, 0)).1) := by
    intro i j hij
    obtain ⟨b, hb⟩ := (ρ j).surjective ((σ (i, 0)).2)
    have he : σ (i, 0) = σ (j, b) := Prod.ext (hij.trans (hf j b).symm) hb.symm
    exact congrArg Prod.fst (σ.injective he)
  let τ : Equiv.Perm (Fin n) :=
    Equiv.ofBijective (fun i : Fin n => (σ (i, 0)).1) ((Finite.injective_iff_bijective).mp hτ)
  refine ⟨τ, ρ, ?_⟩
  apply Equiv.ext
  rintro ⟨i, a⟩
  apply Prod.ext
  · exact (hf i a).symm
  · rfl

theorem symplecticUnit_perm (ρ : Equiv.Perm (Fin 2)) :
    symplecticUnit (ρ 0) (ρ 1) = ((Equiv.Perm.sign ρ : ℤ) : ℂ) := by
  have hs : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
  have hu : ({1, Equiv.swap (0 : Fin 2) 1} : Finset (Equiv.Perm (Fin 2))) = Finset.univ := by
    apply Finset.eq_univ_of_card
    simp [hs, Fintype.card_perm]
  have hm : ρ ∈ ({1, Equiv.swap (0 : Fin 2) 1} : Finset (Equiv.Perm (Fin 2))) := by
    rw [hu]
    exact Finset.mem_univ ρ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with rfl | rfl <;>
    simp [symplecticUnit, Equiv.Perm.sign_swap (by decide : (0 : Fin 2) ≠ 1)]

theorem pairPermutation_summand (n : ℕ) (τ : Equiv.Perm (Fin n))
    (ρ : Fin n → Equiv.Perm (Fin 2)) :
    ((Equiv.Perm.sign (pairPermutation n τ ρ) : ℤ) : ℂ) *
      (∏ i : Fin n, symplecticMatrix n
        (pairPermutation n τ ρ (i, 0)) (pairPermutation n τ ρ (i, 1))) = 1 := by
  simp only [pairPermutation_apply, symplecticMatrix, of_apply, ite_true,
    symplecticUnit_perm, pairPermutation_sign, Units.coe_prod, Int.cast_prod]
  rw [← Finset.prod_mul_distrib]
  have hunit (u : ℤˣ) : ((u : ℤ) : ℂ) * ((u : ℤ) : ℂ) = 1 := by
    have hz : (u : ℤ) * (u : ℤ) = 1 := by
      simp
    exact_mod_cast hz
  simp [hunit]

/-- The explicit factorial normalization gives Pfaffian one on the standard
symplectic form in every dimension. -/
theorem pfaffian_symplecticMatrix (n : ℕ) : pfaffian n (symplecticMatrix n) = 1 := by
  classical
  let term (σ : Equiv.Perm (Fin n × Fin 2)) : ℂ :=
    ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      ∏ i : Fin n, symplecticMatrix n (σ (i, 0)) (σ (i, 1))
  have hz (σ : Equiv.Perm (Fin n × Fin 2)) (hσ : ¬ PreservesPairs n σ) : term σ = 0 := by
    obtain ⟨i, hi⟩ := not_forall.mp hσ
    unfold term
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    simp [symplecticMatrix, hi]
  have hsum : (∑ σ, term σ) =
      ∑ p : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm (Fin 2)),
        term (pairPermutation n p.1 p.2) := by
    calc
      _ = ∑ σ ∈ Finset.univ.filter (PreservesPairs n), term σ := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro σ _ hσ
        apply hz
        simpa using hσ
      _ = _ := by
        symm
        refine Finset.sum_bij (fun p _ => pairPermutation n p.1 p.2) ?_ ?_ ?_ ?_
        · intro p _
          simp [pairPermutation_preserves]
        · intro p _ q _ hpq
          exact pairPermutation_injective n hpq
        · intro σ hσ
          have hp : PreservesPairs n σ := (Finset.mem_filter.mp hσ).2
          obtain ⟨τ, ρ, h⟩ := exists_pairPermutation n σ hp
          exact ⟨(τ, ρ), Finset.mem_univ _, h⟩
        · intro p _
          rfl
  unfold pfaffian
  change (2 ^ n * (n.factorial : ℂ))⁻¹ * (∑ σ, term σ) = 1
  rw [hsum]
  have hterm (p : Equiv.Perm (Fin n) × (Fin n → Equiv.Perm (Fin 2))) :
      term (pairPermutation n p.1 p.2) = 1 := pairPermutation_summand n p.1 p.2
  simp only [hterm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_prod, Fintype.card_perm, Fintype.card_fun, Fintype.card_fin]
  norm_num only [Nat.factorial_two, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  have hn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp

theorem complexify_one (n : ℕ) :
    complexify (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) = 1 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    simp [complexify, Matrix.one_apply, quaternionMatrix_one]
  · simp [complexify, hij, quaternionMatrix_zero]

/-- The signed Moore determinant has the standard identity normalization. -/
theorem mooreDet_identity (n : ℕ) :
    mooreDet n (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) = 1 := by
  unfold mooreDet
  rw [← complexify_mul_symplectic, complexify_one, Matrix.one_mul,
    pfaffian_symplecticMatrix]
  rfl

/-- A block diagonal skew form has the product of its signed two-by-two
entries as its Pfaffian. -/
theorem pfaffian_scalar_blocks (n : ℕ) (d : Fin n → ℂ) :
    pfaffian n (of fun i j => if i.1 = j.1 then d i.1 * symplecticUnit i.2 j.2 else 0) =
      ∏ i, d i := by
  let c : Fin n × Fin 2 → ℂ := fun i => if i.2 = 0 then d i.1 else 1
  have hm : (of fun i j : Fin n × Fin 2 =>
      if i.1 = j.1 then d i.1 * symplecticUnit i.2 j.2 else 0) =
      (of fun i j => c i * symplecticMatrix n i j * c j) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      fin_cases a <;> fin_cases b <;> simp [c, symplecticMatrix, symplecticUnit]
    · simp [symplecticMatrix, hij]
  rw [hm, pfaffian_diagonal_congruence, pfaffian_symplecticMatrix, mul_one]
  simp [c, Fintype.prod_prod_type]

/-- Full signed diagonal normalization: indefinite entries are not replaced
by their absolute values. -/
theorem mooreDet_real_diagonal (n : ℕ) (d : Fin n → ℝ) :
    mooreDet n (Matrix.diagonal (fun i => (d i : Quaternion ℝ))) = ∏ i, d i := by
  have hm : skewComplexify (Matrix.diagonal (fun i => (d i : Quaternion ℝ))) =
      (of fun i j : Fin n × Fin 2 =>
        if i.1 = j.1 then (d i.1 : ℂ) * symplecticUnit i.2 j.2 else 0) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    by_cases hij : i = j
    · subst j
      fin_cases a <;> fin_cases b <;> apply Complex.ext <;>
        simp [skewComplexify, skewQuaternion, quaternionMatrix, symplecticUnit,
          Matrix.mul_apply, Fin.sum_univ_two]
    · simp [skewComplexify, skewQuaternion, hij, quaternionMatrix_zero]
  rw [mooreDet, hm]
  have he := congrArg Complex.re (pfaffian_scalar_blocks n (fun i => (d i : ℂ)))
  simpa only [← Complex.ofReal_prod, Complex.ofReal_re] using he

/-- The Moore determinant of a quaternionic Gram matrix is the determinant
of the faithful complex representation of its factor. -/
theorem mooreDet_gram (n : ℕ) (B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) :
    mooreDet n (B * Bᴴ) = (complexify B).det.re := by
  simpa only [Matrix.mul_one, mooreDet_identity, mul_one] using
    mooreDet_congruence n (1 : Matrix (Fin n) (Fin n) (Quaternion ℝ)) B

/-- Quaternionic unitary matrices have complex determinant one under the
faithful representation, including the sign. -/
theorem complexify_det_of_unitary (n : ℕ)
    (B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hB : B * Bᴴ = 1) :
    (complexify B).det = 1 := by
  apply Complex.ext
  · have h := mooreDet_gram n B
    rw [hB, mooreDet_identity] at h
    exact h.symm
  · exact complexify_det_real n B

/-- Signed Moore determinant invariance under quaternionic unitary change
of coordinates. -/
theorem mooreDet_unitary_congruence (n : ℕ)
    (A B : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hB : B * Bᴴ = 1) :
    mooreDet n (B * A * Bᴴ) = mooreDet n A := by
  rw [mooreDet_congruence, complexify_det_of_unitary n B hB]
  simp

end OAI.LinearAlgebra.Moore
