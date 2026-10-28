import Mathlib

/-! # Congruence -/

namespace OAI.NumberTheory.ArithmeticGroups.Congruence.Level

noncomputable section

open scoped Classical

/-- A root of unity congruent to 1 modulo an integer at least 3 is 1.
The proof uses a conjugate of a nonzero algebraic integer of norm at least 1. -/
theorem integral_root_of_unity_congruence
    {K : Type*} [Field K] [NumberField K]
    (a : K) (ha : IsIntegral ℤ a)
    (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 0 < k)
    (hpow : (1 + (N : K) * a) ^ k = 1) : a = 0 := by
  by_contra hne
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm
    (K := K) (α := ⟨a, ha⟩) (by
      intro h
      exact hne (congrArg (fun x : NumberField.RingOfIntegers K => (x : K)) h))
  have he : (1 + (N : ℂ) * σ a) ^ k = 1 := by
    simpa only [map_pow, map_add, map_one, map_mul, map_natCast] using congrArg σ hpow
  have hn := Complex.norm_eq_one_of_pow_eq_one he hk.ne'
  have hb := norm_sub_le (1 + (N : ℂ) * σ a) 1
  rw [add_sub_cancel_left, norm_mul, Complex.norm_natCast, hn, norm_one] at hb
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  change 1 ≤ ‖σ a‖ at hσ
  nlinarith

theorem complex_integral_root_of_unity_congruence
    (a : ℂ) (ha : IsIntegral ℤ a)
    (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 0 < k)
    (hpow : (1 + (N : ℂ) * a) ^ k = 1) : a = 0 := by
  let K := IntermediateField.adjoin ℚ {a}
  let : NumberField K :=
    { to_charZero := K.charZero
      to_finiteDimensional := IntermediateField.adjoin.finiteDimensional ha.tower_top }
  let α : K := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
  have hi : IsIntegral ℤ α := IntermediateField.coe_isIntegral_iff.mp ha
  have hp : (1 + (N : K) * α) ^ k = 1 := by
    apply Subtype.ext
    exact hpow
  have hz := integral_root_of_unity_congruence α hi N hN k hk hp
  exact congrArg (fun x : K => (x : ℂ)) hz

/-- The eigenvalue argument for congruence torsion, before choosing an integral basis. -/
theorem integral_spectrum_congruence_torsion
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : Module.End ℂ V)
    (ha : ∀ z : ℂ, a.HasEigenvalue z → IsIntegral ℤ z)
    (N : ℕ) (hN : 3 ≤ N) (k : ℕ) (hk : 0 < k)
    (hpow : (1 + (N : ℂ) • a) ^ k = 1) : a = 0 := by
  let f : Module.End ℂ V := 1 + (N : ℂ) • a
  have hNk : (N : ℂ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hf : f.IsSemisimple := by
    apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := Polynomial.X ^ k - Polynomial.C (1 : ℂ))
    · exact (Polynomial.separable_X_pow_sub_C 1 hkC one_ne_zero).squarefree
    · simpa only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        map_one, sub_eq_zero] using hpow
  have has : a.IsSemisimple := by
    have h := hf.aeval (Polynomial.C ((N : ℂ)⁻¹) * (Polynomial.X - 1))
    have he : Polynomial.aeval f
        (Polynomial.C ((N : ℂ)⁻¹) * (Polynomial.X - 1)) = a := by
      simp only [map_mul, map_sub, map_one, Polynomial.aeval_C, Polynomial.aeval_X]
      change ((N : ℂ)⁻¹) • ((1 + (N : ℂ) • a) - 1) = a
      rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hNk, one_smul]
    rwa [he] at h
  apply has.eq_zero_iff_forall_eigenvalue.mpr
  intro z hz
  apply complex_integral_root_of_unity_congruence z (ha z hz) N hN k hk
  obtain ⟨v, hv⟩ := hz.exists_hasEigenvector
  have hfv : f.HasEigenvector (1 + (N : ℂ) * z) v := by
    refine ⟨Module.End.mem_eigenspace_iff.mpr ?_, hv.2⟩
    change v + (N : ℂ) • a v = (1 + (N : ℂ) * z) • v
    rw [hv.apply_eq_smul, add_smul, one_smul, mul_smul]
  have h := hfv.pow_apply k
  change ((1 + (N : ℂ) • a) ^ k) v = (1 + (N : ℂ) * z) ^ k • v at h
  rw [hpow, Module.End.one_apply] at h
  exact (smul_left_injective ℂ hv.2) (h.symm.trans (one_smul ℂ v).symm)

/-- Principal level at any integer N ≥ 3 contains no nonidentity finite-order
integer matrix. No Hermitian signature or special-unitary condition is needed. -/
theorem integer_matrix_congruence_torsion
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℤ) (N : ℕ) (hN : 3 ≤ N)
    (k : ℕ) (hk : 0 < k) (hpow : (1 + N • B) ^ k = 1) : B = 0 := by
  let a : Module.End ℂ (ι → ℂ) := Matrix.toLin' (B.map (Int.castRingHom ℂ))
  have ha : ∀ z : ℂ, a.HasEigenvalue z → IsIntegral ℤ z := by
    intro z hz
    have hr := (Module.End.hasEigenvalue_iff_isRoot_charpoly a z).mp hz
    change (Matrix.toLin' (B.map (Int.castRingHom ℂ))).charpoly.IsRoot z at hr
    rw [Matrix.charpoly_toLin', Matrix.charpoly_map] at hr
    refine ⟨B.charpoly, B.charpoly_monic, ?_⟩
    have he : Int.castRingHom ℂ = algebraMap ℤ ℂ := by ext n; simp
    simpa only [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.aeval_def, he] using hr
  have hp : (1 + (N : ℂ) • a) ^ k = 1 := by
    let F : Matrix ι ι ℤ →+* Module.End ℂ (ι → ℂ) :=
      Matrix.toLinAlgEquiv'.toRingHom.comp (Int.castRingHom ℂ).mapMatrix
    have h := congrArg F hpow
    simp only [map_pow, map_add, map_one, map_nsmul] at h
    change (1 + N • a) ^ k = 1 at h
    simpa only [Nat.cast_smul_eq_nsmul] using h
  have hz := integral_spectrum_congruence_torsion a ha N hN k hk hp
  have hB : B.map (Int.castRingHom ℂ) = 0 := by
    apply Matrix.toLin'.injective
    exact hz.trans (map_zero _).symm
  ext i j
  have h := congrArg (fun M : Matrix ι ι ℂ => M i j) hB
  change (B i j : ℂ) = 0 at h
  exact_mod_cast h

theorem finite_lattice_congruence_torsion
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    [Module.Finite ℤ M] [Module.IsTorsionFree ℤ M]
    (f : Module.End ℤ M) (N : ℕ) (hN : 3 ≤ N)
    (hcong : ∀ x : M, ∃ y : M, f x - x = N • y)
    (k : ℕ) (hk : 0 < k) (hpow : f ^ k = 1) : f = 1 := by
  let b := Module.Free.chooseBasis ℤ M
  let ι := Module.Free.ChooseBasisIndex ℤ M
  let A : Matrix ι ι ℤ := LinearMap.toMatrix b b f
  choose y hy using (fun j : ι => hcong (b j))
  let B : Matrix ι ι ℤ := fun i j => b.repr (y j) i
  have hA : A = 1 + N • B := by
    ext i j
    have h := congrArg (fun x : M => b.repr x i) (hy j)
    change b.repr (f (b j) - b j) i = b.repr (N • y j) i at h
    simp only [map_sub, Finsupp.sub_apply, map_nsmul, Finsupp.smul_apply,
      b.repr_self, Finsupp.single_apply] at h
    simp only [A, LinearMap.toMatrix_apply, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply]
    change b.repr (f (b j)) i = (if i = j then 1 else 0) + N • b.repr (y j) i
    simpa only [eq_comm, nsmul_eq_mul, add_comm] using eq_add_of_sub_eq h
  have hp : A ^ k = 1 := by
    change (LinearMap.toMatrix b b f) ^ k = 1
    rw [LinearMap.toMatrix_pow, hpow]
    exact LinearMap.toMatrix_one b
  have hB : B = 0 := integer_matrix_congruence_torsion B N hN k hk (hA ▸ hp)
  have hf : LinearMap.toMatrix b b f = LinearMap.toMatrix b b (1 : Module.End ℤ M) := by
    rw [← show A = LinearMap.toMatrix b b f from rfl, hA, hB]
    simp
  exact (LinearMap.toMatrix b b).injective hf

end

end OAI.NumberTheory.ArithmeticGroups.Congruence.Level
