import OAI.Geometry.ComplexBall.ArithmeticQuotientEquationsData

/-! # Generation -/

namespace OAI.Geometry.ComplexBall.Generation.ArithmeticQuotient

noncomputable section

section

/-! Elementary-matrix generation and perfectness of SL(3). These are used
to verify semisimplicity of the geometric unitary group after splitting. -/

open scoped BigOperators Classical commutatorElement
open _root_.Matrix _root_.Matrix.SpecialLinearGroup

variable {K : Type*} [Field K]

def blockSL2 : Matrix.SpecialLinearGroup (Fin 2) K →* ArithmeticQuotientEquationsData.SL K where
  toFun A := ⟨!![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1], by
    have h := A.property
    rw [Matrix.det_fin_two] at h
    simpa [Matrix.det_fin_three] using h⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' A B := by
    apply Subtype.ext
    change (!![(A * B) 0 0, (A * B) 0 1, 0;
      (A * B) 1 0, (A * B) 1 1, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) K) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] *
      !![B 0 0, B 0 1, 0; B 1 0, B 1 1, 0; 0, 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ]

def sl3Reindex (e : Equiv.Perm (Fin 3)) : ArithmeticQuotientEquationsData.SL K →* ArithmeticQuotientEquationsData.SL K where
  toFun A := ⟨Matrix.reindex e e A.val, by rw [Matrix.det_reindex_self]; exact A.property⟩
  map_one' := Subtype.ext (map_one (Matrix.reindexRingEquiv K e))
  map_mul' A B := Subtype.ext (map_mul (Matrix.reindexRingEquiv K e) A.val B.val)

lemma blockSL2_coe (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    (blockSL2 A : Matrix (Fin 3) (Fin 3) K) =
      !![A 0 0, A 0 1, 0; A 1 0, A 1 1, 0; 0, 0, 1] := rfl

lemma blockSL2_transvection01 (a : K) :
    blockSL2 (transvection (show (0 : Fin 2) ≠ 1 by decide) a) =
      transvection (show (0 : Fin 3) ≠ 1 by decide) a := by
  apply Subtype.ext
  rw [blockSL2_coe]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe]

lemma blockSL2_transvection10 (a : K) :
    blockSL2 (transvection (show (1 : Fin 2) ≠ 0 by decide) a) =
      transvection (show (1 : Fin 3) ≠ 0 by decide) a := by
  apply Subtype.ext
  rw [blockSL2_coe]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [transvection_coe]

lemma blockSL2_diag2 (a : K) (ha : a ≠ 0) :
    blockSL2 (diag2 a ha) = diag2n (show (0 : Fin 3) ≠ 1 by decide) a ha := by
  apply Subtype.ext
  rw [blockSL2_coe]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [diag2n_coe]

lemma sl3Reindex_transvection (e : Equiv.Perm (Fin 3))
    {i j : Fin 3} (hij : i ≠ j) (a : K) :
    sl3Reindex e (transvection hij a) = transvection (fun h => hij (e.injective h)) a := by
  apply Subtype.ext
  change Matrix.reindex e e (transvection hij a : Matrix (Fin 3) (Fin 3) K) = _
  simp [transvection_coe, Matrix.reindex_apply,
    Matrix.submatrix_add, Matrix.submatrix_one_equiv, Matrix.submatrix_single_equiv]

lemma sl3Reindex_diag2n (e : Equiv.Perm (Fin 3))
    {i j : Fin 3} (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    sl3Reindex e (diag2n hij a ha) = diag2n (fun h => hij (e.injective h)) a ha := by
  apply Subtype.ext
  change Matrix.reindex e e (diag2n hij a ha : Matrix (Fin 3) (Fin 3) K) = _
  apply Matrix.ext
  intro r s
  simp [diag2n_coe, Matrix.reindex_apply, Matrix.diagonal,
    Equiv.symm_apply_eq]

lemma sl3_pair_permutation {i j : Fin 3} (hij : i ≠ j) :
    ∃ e : Equiv.Perm (Fin 3), e 0 = i ∧ e 1 = j := by
  refine ⟨Equiv.swap 0 i * Equiv.swap 1 ((Equiv.swap 0 i) j), ?_, ?_⟩
  all_goals fin_cases i <;> fin_cases j <;> first | contradiction | decide

lemma sl3_pair_hom {i j : Fin 3} (hij : i ≠ j) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) K →* ArithmeticQuotientEquationsData.SL K,
      (∀ a ha, φ (diag2 a ha) = diag2n hij a ha) ∧
      (∀ a, φ (transvection (show (0 : Fin 2) ≠ 1 by decide) a) = transvection hij a) ∧
      (∀ a, φ (transvection (show (1 : Fin 2) ≠ 0 by decide) a) = transvection hij.symm a) := by
  obtain ⟨e, hi, hj⟩ := sl3_pair_permutation hij
  refine ⟨(sl3Reindex e).comp blockSL2, ?_, ?_, ?_⟩
  · intro a ha
    simp only [MonoidHom.comp_apply, blockSL2_diag2, sl3Reindex_diag2n]
    simp only [hi, hj]
  · intro a
    simp only [MonoidHom.comp_apply, blockSL2_transvection01, sl3Reindex_transvection]
    simp only [hi, hj]
  · intro a
    simp only [MonoidHom.comp_apply, blockSL2_transvection10, sl3Reindex_transvection]
    simp only [hi, hj]

lemma sl3_diagonal_decomposition {i j : Fin 3} (hij : i ≠ j) (a : K) (ha : a ≠ 0) :
    diag2n hij a ha =
      transvection hij a * transvection hij.symm (-a⁻¹) * transvection hij a *
      transvection hij (-1) * transvection hij.symm 1 * transvection hij (-1) := by
  obtain ⟨φ, hd, ht, ht'⟩ := sl3_pair_hom (K := K) hij
  simpa only [map_mul, hd, ht, ht'] using congrArg φ (Matrix.diag2_decompose a ha)

theorem sl3_transvection_induction (P : ArithmeticQuotientEquationsData.SL K → Prop)
    (ht : ∀ (i j : Fin 3) (hij : i ≠ j) (a : K), P (transvection hij a))
    (hm : ∀ A B, P A → P B → P (A * B)) (A : ArithmeticQuotientEquationsData.SL K) : P A := by
  apply diagonal_transvection_induction' P A _ ht hm
  intro i j hij a ha
  rw [sl3_diagonal_decomposition hij a ha]
  exact hm _ _ (hm _ _ (hm _ _ (hm _ _ (hm _ _ (ht _ _ _ _) (ht _ _ _ _))
    (ht _ _ _ _)) (ht _ _ _ _)) (ht _ _ _ _)) (ht _ _ _ _)

lemma sl3_transvection_as_commutator [CharZero K] {i j : Fin 3} (hij : i ≠ j) (a : K) :
    ⁅diag2n hij (2 : K) (by norm_num), transvection hij (a / 3)⁆ = transvection hij a := by
  obtain ⟨φ, hd, ht, ht'⟩ := sl3_pair_hom (K := K) hij
  have hc : a = (a / 3) * ((2 : K) ^ 2 - 1) := by field_simp; ring
  have h := congrArg φ (Matrix.commutator_diag2_transvection (2 : K) (by norm_num) (a / 3) a hc)
  simpa only [map_commutatorElement, hd, ht] using h

theorem sl3_commutator_eq_top [CharZero K] : commutator (ArithmeticQuotientEquationsData.SL K) = ⊤ := by
  apply top_unique
  intro g _
  apply sl3_transvection_induction (fun g : ArithmeticQuotientEquationsData.SL K => g ∈ commutator (ArithmeticQuotientEquationsData.SL K)) _ _ g
  · intro i j hij a
    rw [← sl3_transvection_as_commutator hij a]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · exact fun _ _ => mul_mem

end

/-! A solvable normal subgroup of SL(3) in characteristic zero is central.
The proof uses its action on projective space and the Iwasawa criterion. -/

open scoped Classical LinearAlgebra.Projectivization Pointwise
open _root_.Matrix _root_.Matrix.SpecialLinearGroup MulAction

variable {K : Type*} [Field K]

instance sl3Nontrivial : Nontrivial (ArithmeticQuotientEquationsData.SL K) := by
  refine ⟨⟨transvection (show (0 : Fin 3) ≠ 1 by decide) 1, 1, ?_⟩⟩
  intro h
  have he := congrArg (fun g : ArithmeticQuotientEquationsData.SL K => g.val 0 1) h
  simp [transvection_coe] at he

theorem sl3_iSup_lineStab :
    (⨆ p : ℙ K (Fin 3 → K), lineStab p.submodule) = (⊤ : Subgroup (ArithmeticQuotientEquationsData.SL K)) := by
  apply top_unique
  intro g _
  apply sl3_transvection_induction (fun g : ArithmeticQuotientEquationsData.SL K =>
    g ∈ (⨆ p : ℙ K (Fin 3 → K), lineStab p.submodule)) _ _ g
  · intro i j hij a
    let p : ℙ K (Fin 3 → K) :=
      Projectivization.mk K (Pi.single i 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)
    apply (le_iSup (fun p : ℙ K (Fin 3 → K) => lineStab p.submodule) p)
    change transvection hij a ∈ lineStab
      (Projectivization.mk K (Pi.single i 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)).submodule
    rw [Projectivization.submodule_mk]
    exact SL2Gen.transvection_mem_lineStab hij a
  · exact fun _ _ => mul_mem

def sl3Iwasawa : IwasawaStructure (ArithmeticQuotientEquationsData.SL K) (ℙ K (Fin 3 → K)) where
  T p := lineStab p.submodule
  is_comm p := by
    rw [← Projectivization.mk_rep p, Projectivization.submodule_mk]
    exact lineStab_isMulCommutative_of_span p.rep p.rep_nonzero
  is_conj g p := by rw [PSL.smul_submodule, lineStab_smul]
  is_generator := sl3_iSup_lineStab

theorem sl3_solvable_normal_central [CharZero K]
    (N : Subgroup (ArithmeticQuotientEquationsData.SL K)) (hN : N.Normal) (hsolv : Group.IsSolvable N) :
    N ≤ Subgroup.center (ArithmeticQuotientEquationsData.SL K) := by
  let := hN
  let := hsolv
  let : Group.IsPerfect (ArithmeticQuotientEquationsData.SL K) := ⟨sl3_commutator_eq_top⟩
  have hfix : fixedPoints N (ℙ K (Fin 3 → K)) = Set.univ := by
    by_contra h
    have htop : N = ⊤ := top_unique (by
      simpa only [sl3_commutator_eq_top] using sl3Iwasawa.commutator_le N h)
    have hG : Group.IsSolvable (ArithmeticQuotientEquationsData.SL K) := by
      subst N
      exact Group.isSolvable_of_surjective (f := (⊤ : Subgroup (ArithmeticQuotientEquationsData.SL K)).subtype)
        (fun g => ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩)
    exact Group.IsPerfect.not_isSolvable (ArithmeticQuotientEquationsData.SL K) hG
  intro g hg
  apply (QuotientGroup.eq_one_iff g).mp
  apply eq_of_smul_eq_smul (α := ℙ K (Fin 3 → K))
  intro p
  have hp : p ∈ fixedPoints N (ℙ K (Fin 3 → K)) := by rw [hfix]; trivial
  have hh := hp (⟨g, hg⟩ : N)
  change g • p = p at hh
  simpa only [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk, one_smul] using hh

end

end OAI.Geometry.ComplexBall.Generation.ArithmeticQuotient
