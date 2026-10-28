import Mathlib

/-! # Elementary Divisors Existence Linear -/

namespace OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction

section

open scoped BigOperators

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma uniformizer_map_ne_zero {π : R} (hπ : Irreducible π) :
    algebraMap R K π ≠ 0 := by
  exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 hπ.ne_zero

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma integral_zpow_iff {π : R} (hπ : Irreducible π) (a : ℤ) :
    (∃ r : R, algebraMap R K r = (algebraMap R K π) ^ a) ↔ 0 ≤ a := by
  constructor
  · rintro ⟨r, hr⟩
    by_contra hn
    have hn' : a < 0 := lt_of_not_ge hn
    obtain ⟨m, hm⟩ := Int.eq_negSucc_of_lt_zero hn'
    subst a
    have he : r * π ^ (m + 1) = 1 := by
      apply IsFractionRing.injective R K
      simp only [map_mul, map_pow, map_one, hr, zpow_negSucc]
      exact inv_mul_cancel₀ (pow_ne_zero _ (uniformizer_map_ne_zero hπ))
    have hu : IsUnit (π ^ (m + 1)) := IsUnit.of_mul_eq_one_right r he
    rw [pow_succ] at hu
    exact hπ.not_isUnit (IsUnit.mul_iff.mp hu).2
  · intro ha
    refine ⟨π ^ a.toNat, ?_⟩
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg ha]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma gl3_determinant_unit_adjustment
    (g : Matrix.GeneralLinearGroup (Fin 3) K)
    (hdet : ∃ u : Rˣ, g.val.det = algebraMap R K (u : R)) :
    ∃ U : Matrix.GeneralLinearGroup (Fin 3) R,
      (g.val * U.val.map (algebraMap R K)).det = 1 := by
  obtain ⟨u, hu⟩ := hdet
  obtain ⟨U, hU⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin 3) u⁻¹
  refine ⟨U, ?_⟩
  rw [Matrix.det_mul, hu]
  change algebraMap R K (u : R) *
    ((algebraMap R K).mapMatrix U.val).det = 1
  rw [← RingHom.map_det]
  have hU' : U.val.det = (↑u⁻¹ : R) := congrArg Units.val hU
  rw [hU', ← map_mul]
  simp

lemma exists_unit_permutation {n : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, IsUnit (A (σ i) i) := by
  classical
  rw [Matrix.det_apply] at hA
  obtain ⟨σ, _, hσ⟩ := IsLocalRing.exists_of_isUnit_sum hA
  refine ⟨σ, ?_⟩
  have hσ' : IsUnit ((↑(Equiv.Perm.sign σ) : R) * ∏ i, A (σ i) i) := by
    simpa only [Units.smul_def, zsmul_eq_mul] using hσ
  have hp : IsUnit (∏ i, A (σ i) i) := (IsUnit.mul_iff.mp hσ').2
  simpa using (IsUnit.prod_univ_iff.mp hp)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma exponent_le_of_unit_coefficient {π : R} (hπ : Irreducible π)
    {a b : ℤ} {u r : R} (hu : IsUnit u)
    (h : algebraMap R K u * (algebraMap R K π) ^ b =
      algebraMap R K r * (algebraMap R K π) ^ a) : a ≤ b := by
  obtain ⟨u, rfl⟩ := hu
  have hp := uniformizer_map_ne_zero (K := K) hπ
  have hi : ∃ s : R, algebraMap R K s = (algebraMap R K π) ^ (b - a) := by
    refine ⟨(↑u⁻¹ : R) * r, ?_⟩
    rw [map_mul, zpow_sub₀ hp]
    apply (eq_div_iff (zpow_ne_zero _ hp)).2
    calc
      _ = algebraMap R K (↑u⁻¹ : R) *
          (algebraMap R K r * (algebraMap R K π) ^ a) := by ring
      _ = algebraMap R K (↑u⁻¹ : R) *
          (algebraMap R K (u : R) * (algebraMap R K π) ^ b) := by rw [← h]
      _ = _ := by rw [← mul_assoc, ← map_mul]; simp
  have := (integral_zpow_iff (K := K) hπ (b - a)).mp hi
  omega

lemma monotone_eq_of_permutation_bounds {n : ℕ} {a b : Fin n → ℤ}
    (ha : Monotone a) (hb : Monotone b)
    (h₁ : ∃ σ : Equiv.Perm (Fin n), ∀ i, a (σ i) ≤ b i)
    (h₂ : ∃ τ : Equiv.Perm (Fin n), ∀ i, b (τ i) ≤ a i) : a = b := by
  classical
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  have hs₁ : (∑ i, a i) ≤ ∑ i, b i := by
    simpa only [Equiv.sum_comp] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hσ i)
  have hs₂ : (∑ i, b i) ≤ ∑ i, a i := by
    simpa only [Equiv.sum_comp] using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hτ i)
  have hs : (∑ i, a (σ i)) = ∑ i, b i := by
    simpa only [Equiv.sum_comp] using le_antisymm hs₁ hs₂
  have he : a ∘ σ = b := funext fun i =>
    (Finset.sum_eq_sum_iff_of_le (fun j (_ : j ∈ Finset.univ) => hσ j)).mp hs i (Finset.mem_univ i)
  have hm : Monotone (a ∘ σ) := he.symm ▸ hb
  have hu := Tuple.unique_monotone (σ := Equiv.refl (Fin n)) (τ := σ) ha hm
  exact hu.trans he

end

section

open _root_.Module
open scoped BigOperators

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : ℕ}

noncomputable def powerBasis (π : R) (hπ : Irreducible π)
    (e : Basis (Fin n) K (Fin n → K)) (a : Fin n → ℤ) :
    Basis (Fin n) K (Fin n → K) :=
  e.unitsSMul fun i => Units.mk0 ((algebraMap R K π) ^ a i)
    (zpow_ne_zero _ (uniformizer_map_ne_zero hπ))

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp] lemma powerBasis_apply (π : R) (hπ : Irreducible π)
    (e : Basis (Fin n) K (Fin n → K)) (a : Fin n → ℤ) (i : Fin n) :
    powerBasis π hπ e a i = (algebraMap R K π) ^ a i • e i := by
  simp [powerBasis, Basis.unitsSMul_apply, Units.smul_def]

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp] lemma powerBasis_repr (π : R) (hπ : Irreducible π)
    (e : Basis (Fin n) K (Fin n → K)) (a : Fin n → ℤ)
    (x : Fin n → K) (i : Fin n) :
    (powerBasis π hπ e a).repr x i =
      ((algebraMap R K π) ^ a i)⁻¹ * e.repr x i := by
  simp [powerBasis, Basis.repr_unitsSMul, Units.smul_def]

lemma lattice_basis_permutation_bound (π : R) (hπ : Irreducible π)
    (e f : Basis (Fin n) K (Fin n → K)) (a b : Fin n → ℤ)
    (h₀ : Submodule.span R (Set.range e) = Submodule.span R (Set.range f))
    (h₁ : Submodule.span R (Set.range (powerBasis π hπ e a)) =
      Submodule.span R (Set.range (powerBasis π hπ f b))) :
    ∃ σ : Equiv.Perm (Fin n), ∀ i, a (σ i) ≤ b i := by
  classical
  let eb := e.restrictScalars R
  let fb := (f.restrictScalars R).map (LinearEquiv.ofEq _ _ h₀.symm)
  let A := eb.toMatrix fb
  let := eb.invertibleToMatrix fb
  have hu : IsUnit A.det := Matrix.isUnit_det_of_invertible A
  obtain ⟨σ, hσ⟩ := exists_unit_permutation A hu
  refine ⟨σ, fun i => ?_⟩
  have hc : algebraMap R K (A (σ i) i) = e.repr (f i) (σ i) := by
    simpa only [A, eb, Basis.toMatrix_apply, fb, Basis.map_apply,
      LinearEquiv.coe_ofEq_apply, Basis.restrictScalars_apply] using
      e.restrictScalars_repr_apply R (fb i) (σ i)
  have hm : powerBasis π hπ f b i ∈
      Submodule.span R (Set.range (powerBasis π hπ e a)) := by
    rw [h₁]
    exact Submodule.subset_span (Set.mem_range_self i)
  obtain ⟨r, hr⟩ := ((powerBasis π hπ e a).mem_span_iff_repr_mem R _).mp hm (σ i)
  apply exponent_le_of_unit_coefficient (K := K) hπ (hσ i) (r := r)
  rw [hc, hr]
  simp only [powerBasis_repr, powerBasis_apply, map_smul, Finsupp.smul_apply,
    smul_eq_mul]
  field_simp [uniformizer_map_ne_zero (K := K) hπ]

lemma lattice_exponents_unique (π : R) (hπ : Irreducible π)
    (e f : Basis (Fin n) K (Fin n → K)) (a b : Fin n → ℤ)
    (ha : Monotone a) (hb : Monotone b)
    (h₀ : Submodule.span R (Set.range e) = Submodule.span R (Set.range f))
    (h₁ : Submodule.span R (Set.range fun i => (algebraMap R K π) ^ a i • e i) =
      Submodule.span R (Set.range fun i => (algebraMap R K π) ^ b i • f i)) :
    a = b := by
  have h₁' : Submodule.span R (Set.range (powerBasis π hπ e a)) =
      Submodule.span R (Set.range (powerBasis π hπ f b)) := by
    change Submodule.span R (Set.range fun i => powerBasis π hπ e a i) =
      Submodule.span R (Set.range fun i => powerBasis π hπ f b i)
    simpa only [powerBasis_apply] using h₁
  exact monotone_eq_of_permutation_bounds ha hb
    (lattice_basis_permutation_bound π hπ e f a b h₀ h₁')
    (lattice_basis_permutation_bound π hπ f e b a h₀.symm h₁'.symm)

end

section

open _root_.Module
open scoped BigOperators Pointwise

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : ℕ}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma basis_span_coe {L : Submodule R (Fin n → K)} (b : Basis (Fin n) R L) :
    Submodule.span R (Set.range fun i => (b i : Fin n → K)) = L := by
  have h := congrArg (Submodule.map L.subtype) b.span_eq
  simpa only [Submodule.map_span, ← Set.range_comp, Submodule.map_top,
    Submodule.range_subtype, Function.comp_def, Submodule.coe_subtype] using h

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma extended_basis_span {L : Submodule R (Fin n → K)} [Submodule.IsLattice K L]
    (b : Basis (Fin n) R L) :
    Submodule.span R (Set.range (b.extendOfIsLattice K)) = L := by
  change Submodule.span R (Set.range fun i => b.extendOfIsLattice K i) = L
  simpa only [Basis.extendOfIsLattice_apply] using basis_span_coe b

lemma lattice_exists_scale_le (L M : Submodule R (Fin n → K))
    [Submodule.IsLattice K L] [Submodule.IsLattice K M] :
    ∃ q : Kˣ, q • M ≤ L := by
  classical
  have hnL : Module.finrank R L = n := by simpa using Submodule.IsLattice.finrank_of_pi K L
  have hnM : Module.finrank R M = n := by simpa using Submodule.IsLattice.finrank_of_pi K M
  let bl : Basis (Fin n) R L := Module.finBasisOfFinrankEq R L hnL
  let bm : Basis (Fin n) R M := Module.finBasisOfFinrankEq R M hnM
  let e := bl.extendOfIsLattice K
  let f := bm.extendOfIsLattice K
  have he : Submodule.span R (Set.range e) = L := extended_basis_span (K := K) (L := L) bl
  have hf : Submodule.span R (Set.range f) = M := extended_basis_span (K := K) (L := M) bm
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun ij : Fin n × Fin n => e.repr (f ij.2) ij.1)
  have hc0 : algebraMap R K (c : R) ≠ 0 := by
    exact (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2
      (mem_nonZeroDivisors_iff_ne_zero.mp c.property)
  let q : Kˣ := Units.mk0 (algebraMap R K (c : R)) hc0
  refine ⟨q, ?_⟩
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists x q M).mp hx
  clear hx
  rw [← hf] at hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      rw [← he, e.mem_span_iff_repr_mem R]
      intro j
      change ∃ r : R, algebraMap R K r =
        e.repr ((algebraMap R K (c : R)) • f i) j
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      obtain ⟨r, hr⟩ := hc (j, i)
      exact ⟨r, by simpa only [Algebra.smul_def] using hr⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [smul_add] using L.add_mem hx hy
  | smul r x _ hx => simpa only [smul_comm q r x] using L.smul_mem r hx

end

section

open _root_.Module
open scoped BigOperators Pointwise

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : ℕ}

lemma lattice_diagonal_exists (π : R) (hπ : Irreducible π)
    (L M : Submodule R (Fin n → K))
    [Submodule.IsLattice K L] [Submodule.IsLattice K M] :
    ∃ (a : Fin n → ℤ) (e : Basis (Fin n) K (Fin n → K)),
      L = Submodule.span R (Set.range e) ∧
      M = Submodule.span R (Set.range fun i => (algebraMap R K π) ^ a i • e i) := by
  classical
  obtain ⟨q, hq⟩ := lattice_exists_scale_le L M
  let N : Submodule R (Fin n → K) := q • M
  let J : Submodule R L := N.comap L.subtype
  let E : J ≃ₗ[R] N := Submodule.comapSubtypeEquivOfLe hq
  have hnL : Module.finrank R L = n := by simpa using Submodule.IsLattice.finrank_of_pi K L
  have hnN : Module.finrank R N = n := by simpa using Submodule.IsLattice.finrank_of_pi K N
  have hj : Module.finrank R J = Module.finrank R L := E.finrank_eq.trans (hnN.trans hnL.symm)
  let bl : Basis (Fin n) R L := Module.finBasisOfFinrankEq R L hnL
  obtain ⟨b, d, c, hc⟩ := J.exists_smith_normal_form_of_rank_eq bl hj
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    apply c.ne_zero i
    apply Subtype.ext
    change (c i : L) = 0
    simpa only [hi, zero_smul] using hc i
  have hx : ∀ i, (↑q⁻¹ : K) * algebraMap R K (d i) ≠ 0 := by
    intro i
    exact mul_ne_zero (Units.ne_zero _) ((map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (hd i))
  choose a u hu using fun i =>
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ (hx i)
  let e := (b.unitsSMul u).extendOfIsLattice K
  have he : Submodule.span R (Set.range e) = L :=
    extended_basis_span (K := K) (L := L) (b.unitsSMul u)
  let f : Fin n → (Fin n → K) := fun i => ((c i : L) : Fin n → K)
  have hf : Submodule.span R (Set.range f) = N := by
    simpa [f, E, Basis.map_apply, Submodule.comapSubtypeEquivOfLe]
      using basis_span_coe (c.map E)
  have hv : ∀ i, (algebraMap R K π) ^ a i • e i = q⁻¹ • f i := by
    intro i
    have hi : (↑q⁻¹ : K) * algebraMap R K (d i) =
        algebraMap R K (u i : R) * (algebraMap R K π) ^ a i := by
      simpa only [Units.smul_def, Algebra.smul_def] using hu i
    have hci : f i = algebraMap R K (d i) • (b i : Fin n → K) := by
      change ((c i : L) : Fin n → K) = _
      rw [hc i]
      simp only [Submodule.coe_smul, algebraMap_smul]
    have hei : e i = algebraMap R K (u i : R) • (b i : Fin n → K) := by
      simp only [e, Basis.extendOfIsLattice_apply, Basis.unitsSMul_apply,
        Units.smul_def, Submodule.coe_smul, algebraMap_smul]
    rw [hei, hci, Units.smul_def, smul_smul, smul_smul, hi, mul_comm]
  refine ⟨a, e, he.symm, ?_⟩
  simp_rw [hv]
  rw [Set.range_smul, ← Submodule.smul_span, hf]
  exact (inv_smul_smul q M).symm

lemma lattices_elementary_divisors
    (π : R) (hπ : Irreducible π)
    (L M : Submodule R (Fin n → K))
    [Submodule.IsLattice K L] [Submodule.IsLattice K M] :
    ∃! a : Fin n → ℤ,
      Monotone a ∧
      ∃ e : Basis (Fin n) K (Fin n → K),
        L = Submodule.span R (Set.range fun i => e i) ∧
        M = Submodule.span R
          (Set.range fun i => (algebraMap R K π) ^ a i • e i) := by
  classical
  obtain ⟨a, e, he, ha⟩ := lattice_diagonal_exists π hπ L M
  let σ := Tuple.sort a
  let f := e.reindex σ.symm
  have hfL : L = Submodule.span R (Set.range f) := by
    simpa only [f, Basis.coe_reindex, Equiv.symm_symm, σ.surjective.range_comp] using he
  have hfM : M = Submodule.span R
      (Set.range fun i => (algebraMap R K π) ^ (a ∘ σ) i • f i) := by
    simp only [f, Basis.reindex_apply, Equiv.symm_symm, Function.comp_apply]
    change M = Submodule.span R
      (Set.range ((fun i => (algebraMap R K π) ^ a i • e i) ∘ σ))
    rw [σ.surjective.range_comp]
    exact ha
  refine ⟨a ∘ σ, ⟨Tuple.monotone_sort a, f, hfL, hfM⟩, ?_⟩
  rintro b ⟨hb, g, hg, hbg⟩
  exact lattice_exponents_unique π hπ g f b (a ∘ σ) hb (Tuple.monotone_sort a)
    (hg.symm.trans hfL) (hbg.symm.trans hfM)

end

section

open _root_.Module _root_.Matrix
open scoped BigOperators

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : ℕ}

noncomputable def matrixBasis (g : Matrix.GeneralLinearGroup (Fin n) K) :
    Basis (Fin n) K (Fin n → K) := by
  classical
  exact basisOfPiSpaceOfLinearIndependent (Matrix.linearIndependent_cols_of_det_ne_zero g.det_ne_zero)

@[simp] lemma matrixBasis_apply (g : Matrix.GeneralLinearGroup (Fin n) K) (i j : Fin n) :
    matrixBasis g i j = g.val j i := by
  classical
  have he : (matrixBasis g : Fin n → Fin n → K) = g.val.col := by
    simpa only [matrixBasis] using
      coe_basisOfPiSpaceOfLinearIndependent
        (Matrix.linearIndependent_cols_of_det_ne_zero g.det_ne_zero)
  exact congrFun (congrFun he i) j

@[simp] lemma standard_toMatrix_matrixBasis (g : Matrix.GeneralLinearGroup (Fin n) K) :
    (Pi.basisFun K (Fin n)).toMatrix (matrixBasis g) = g.val := by
  ext i j
  simp [Basis.toMatrix_apply]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
lemma basis_span_isLattice (e : Basis (Fin n) K (Fin n → K)) :
    Submodule.IsLattice K (Submodule.span R (Set.range e)) where
  fg := Submodule.fg_span (Set.finite_range _)
  span_eq_top := by rw [Submodule.span_span_of_tower, e.span_eq]

lemma integral_basis_change (e f : Basis (Fin n) K (Fin n → K))
    (h : Submodule.span R (Set.range e) = Submodule.span R (Set.range f)) :
    ∃ U : Matrix.GeneralLinearGroup (Fin n) R,
      e.toMatrix f = U.val.map (algebraMap R K) := by
  classical
  let eb := e.restrictScalars R
  let fb := (f.restrictScalars R).map (LinearEquiv.ofEq _ _ h.symm)
  let U : Matrix.GeneralLinearGroup (Fin n) R :=
    ⟨eb.toMatrix fb, fb.toMatrix eb, eb.toMatrix_mul_toMatrix_flip fb,
      fb.toMatrix_mul_toMatrix_flip eb⟩
  refine ⟨U, ?_⟩
  ext i j
  symm
  simpa only [U, Matrix.map_apply, Basis.toMatrix_apply, eb, fb, Basis.map_apply,
    LinearEquiv.coe_ofEq_apply, Basis.restrictScalars_apply] using
    e.restrictScalars_repr_apply R (fb j) i

lemma basis_span_le_of_toMatrix_map (e f : Basis (Fin n) K (Fin n → K))
    (A : Matrix (Fin n) (Fin n) R)
    (h : e.toMatrix f = A.map (algebraMap R K)) :
    Submodule.span R (Set.range f) ≤ Submodule.span R (Set.range e) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  apply (e.mem_span_iff_repr_mem R _).mpr
  intro i
  exact ⟨A i j, (congrFun (congrFun h i) j).symm⟩

lemma basis_span_eq_of_toMatrix_map (e f : Basis (Fin n) K (Fin n → K))
    (U : Matrix.GeneralLinearGroup (Fin n) R)
    (h : e.toMatrix f = U.val.map (algebraMap R K)) :
    Submodule.span R (Set.range e) = Submodule.span R (Set.range f) := by
  have hU : f.toMatrix e = (U⁻¹).val.map (algebraMap R K) := by
    have hprod := f.toMatrix_mul_toMatrix_flip e
    rw [h] at hprod
    calc
      _ = f.toMatrix e *
          (U.val.map (algebraMap R K) * (U⁻¹).val.map (algebraMap R K)) := by
            rw [Matrix.GeneralLinearGroup.coe_inv, Matrix.GeneralLinearGroup.coe_map_mul_map_inv]
            simp
      _ = _ := by rw [← mul_assoc, hprod, one_mul]
  exact le_antisymm (basis_span_le_of_toMatrix_map f e _ hU)
    (basis_span_le_of_toMatrix_map e f _ h)

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma toMatrix_powerBasis (π : R) (hπ : Irreducible π)
    (e : Basis (Fin n) K (Fin n → K)) (a : Fin n → ℤ) :
    e.toMatrix (powerBasis π hπ e a) =
      Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) := by
  classical
  simp [powerBasis, Basis.toMatrix_unitsSMul]

end

section

open _root_.Module _root_.Matrix
open scoped BigOperators

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
variable {n : ℕ}

lemma matrix_factorization_lattices (π : R) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin n) K) (a : Fin n → ℤ)
    (U V : Matrix.GeneralLinearGroup (Fin n) R)
    (h : g.val = U.val.map (algebraMap R K) *
      Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
      V.val.map (algebraMap R K)) :
    ∃ e : Basis (Fin n) K (Fin n → K),
      Submodule.span R (Set.range (Pi.basisFun K (Fin n))) = Submodule.span R (Set.range e) ∧
      Submodule.span R (Set.range (matrixBasis g)) =
        Submodule.span R (Set.range fun i => (algebraMap R K π) ^ a i • e i) := by
  classical
  let s := Pi.basisFun K (Fin n)
  let e := matrixBasis (Matrix.GeneralLinearGroup.map (algebraMap R K) U)
  let f := matrixBasis g
  let p := powerBasis π hπ e a
  have he : s.toMatrix e = U.val.map (algebraMap R K) :=
    standard_toMatrix_matrixBasis _
  have hp : s.toMatrix p = U.val.map (algebraMap R K) *
      Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) := by
    rw [← s.toMatrix_mul_toMatrix e p, he, toMatrix_powerBasis]
  have hg : s.toMatrix f = s.toMatrix p * V.val.map (algebraMap R K) := by
    rw [hp, standard_toMatrix_matrixBasis]
    exact h
  have hV : p.toMatrix f = V.val.map (algebraMap R K) := by
    calc
      _ = p.toMatrix s * s.toMatrix f := (p.toMatrix_mul_toMatrix s f).symm
      _ = _ := by rw [hg, ← mul_assoc, p.toMatrix_mul_toMatrix_flip s, one_mul]
  refine ⟨e, basis_span_eq_of_toMatrix_map s e U he, ?_⟩
  have hm := (basis_span_eq_of_toMatrix_map p f V hV).symm
  change Submodule.span R (Set.range f) =
    Submodule.span R (Set.range fun i => (algebraMap R K π) ^ a i • e i)
  simpa only [p, ← powerBasis_apply π hπ e a] using hm

theorem gl_smith_normal_form (π : R) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin n) K) :
    ∃! a : Fin n → ℤ,
      Monotone a ∧
      ∃ U V : Matrix.GeneralLinearGroup (Fin n) R,
        g.val = U.val.map (algebraMap R K) *
          Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
          V.val.map (algebraMap R K) := by
  classical
  let s := Pi.basisFun K (Fin n)
  let f := matrixBasis g
  let L := Submodule.span R (Set.range s)
  let M := Submodule.span R (Set.range f)
  have : Submodule.IsLattice K L := basis_span_isLattice s
  have : Submodule.IsLattice K M := basis_span_isLattice f
  obtain ⟨a, ⟨ha, e, he, hf⟩, huniq⟩ := lattices_elementary_divisors π hπ L M
  let p := powerBasis π hπ e a
  obtain ⟨U, hU⟩ := integral_basis_change s e he
  have hp : Submodule.span R (Set.range p) = Submodule.span R (Set.range f) := by
    change Submodule.span R (Set.range fun i => powerBasis π hπ e a i) = M
    simpa only [powerBasis_apply] using hf.symm
  obtain ⟨V, hV⟩ := integral_basis_change p f hp
  have hm : g.val = U.val.map (algebraMap R K) *
      Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
      V.val.map (algebraMap R K) := by
    calc
      g.val = s.toMatrix f := (standard_toMatrix_matrixBasis g).symm
      _ = s.toMatrix e * e.toMatrix p * p.toMatrix f := by
        rw [s.toMatrix_mul_toMatrix, s.toMatrix_mul_toMatrix]
      _ = _ := by rw [hU, hV, toMatrix_powerBasis]
  refine ⟨a, ⟨ha, U, V, hm⟩, ?_⟩
  rintro b ⟨hb, U', V', hg⟩
  obtain ⟨e', hL, hM⟩ := matrix_factorization_lattices π hπ g b U' V' hg
  exact huniq b ⟨hb, e', hL, hM⟩

theorem gl3_smith_normal_form
    (π : R) (hπ : Irreducible π)
    (g : Matrix.GeneralLinearGroup (Fin 3) K) :
    ∃! a : Fin 3 → ℤ,
      Monotone a ∧
      ∃ U V : Matrix.GeneralLinearGroup (Fin 3) R,
        g.val = U.val.map (algebraMap R K) *
          Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
          V.val.map (algebraMap R K) :=
  gl_smith_normal_form π hπ g

end

open _root_.Module _root_.Matrix
open scoped BigOperators

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma exponent_zero_of_unit (π : R) (hπ : Irreducible π) (a : ℤ) (u : Rˣ)
    (h : (algebraMap R K π) ^ a = algebraMap R K (u : R)) : a = 0 := by
  have hp := (integral_zpow_iff (K := K) hπ a).mp ⟨u, h.symm⟩
  have hm := (integral_zpow_iff (K := K) hπ (-a)).mp
    ⟨↑u⁻¹, by rw [map_units_inv, _root_.zpow_neg, h]⟩
  omega

omit [IsDomain R] [IsDiscreteValuationRing R] in
lemma determinant_exponent_zero (π : R) (hπ : Irreducible π)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) (a : Fin 3 → ℤ)
    (U V : Matrix.GeneralLinearGroup (Fin 3) R)
    (h : (g : Matrix (Fin 3) (Fin 3) K) = U.val.map (algebraMap R K) *
      Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
      V.val.map (algebraMap R K)) :
    (∑ i, a i) = 0 ∧ U.val.det * V.val.det = 1 := by
  have hp := uniformizer_map_ne_zero (K := K) hπ
  have hd := congrArg Matrix.det h
  have hmap (B : Matrix (Fin 3) (Fin 3) R) :
      (B.map (algebraMap R K)).det = algebraMap R K B.det :=
    ((algebraMap R K).map_det B).symm
  have hprod : (∏ i, (algebraMap R K π) ^ a i) = (algebraMap R K π) ^ (∑ i, a i) := by
    simp [Fin.prod_univ_succ, Fin.sum_univ_succ, zpow_add₀ hp]
  rw [g.property, Matrix.det_mul, Matrix.det_mul, hmap, hmap,
    Matrix.det_diagonal, hprod] at hd
  let u : Rˣ := U.det * V.det
  have he : (algebraMap R K π) ^ (∑ i, a i) = algebraMap R K (↑u⁻¹ : R) := by
    rw [map_units_inv, inv_eq_one_div]
    apply (eq_div_iff ((u.isUnit.map (algebraMap R K)).ne_zero)).mpr
    change (algebraMap R K π) ^ (∑ i, a i) * algebraMap R K (U.val.det * V.val.det) = 1
    rw [map_mul]
    calc
      _ = algebraMap R K U.val.det * (algebraMap R K π) ^ (∑ i, a i) *
          algebraMap R K V.val.det := by ring
      _ = 1 := hd.symm
  have hs := exponent_zero_of_unit π hπ (∑ i, a i) u⁻¹ he
  refine ⟨hs, ?_⟩
  apply IsFractionRing.injective R K
  rw [map_mul, map_one]
  simpa only [hs, zpow_zero, mul_one] using hd.symm

def determinantDiagonal (u : Rˣ) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![(u : R), 1, 1]

omit [IsDomain R] [IsDiscreteValuationRing R] in
@[simp] lemma determinantDiagonal_det (u : Rˣ) : (determinantDiagonal u).det = (u : R) := by
  simp [determinantDiagonal, Matrix.det_diagonal, Fin.prod_univ_succ]

lemma determinantDiagonal_cancel (u : Rˣ) (d : Fin 3 → K) :
    (determinantDiagonal u⁻¹).map (algebraMap R K) * Matrix.diagonal d *
      (determinantDiagonal u).map (algebraMap R K) = Matrix.diagonal d := by
  classical
  simp only [determinantDiagonal, Matrix.diagonal_map (map_zero (algebraMap R K)),
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> simp [map_units_inv, mul_comm]

theorem sl3_smith_normal_form
    (π : R) (hπ : Irreducible π)
    (g : Matrix.SpecialLinearGroup (Fin 3) K) :
    ∃! a : Fin 3 → ℤ,
      Monotone a ∧ (∑ i, a i) = 0 ∧
      ∃ U V : Matrix.SpecialLinearGroup (Fin 3) R,
        (g : Matrix (Fin 3) (Fin 3) K) =
          (U : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) *
          Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
          (V : Matrix (Fin 3) (Fin 3) R).map (algebraMap R K) := by
  classical
  obtain ⟨a, ⟨ha, U, V, h⟩, huniq⟩ :=
    gl3_smith_normal_form π hπ (Matrix.SpecialLinearGroup.toGL g)
  obtain ⟨hs, hd⟩ := determinant_exponent_zero π hπ g a U V h
  let U' : Matrix.SpecialLinearGroup (Fin 3) R :=
    ⟨U.val * determinantDiagonal U.det⁻¹, by
      rw [Matrix.det_mul, determinantDiagonal_det]
      exact Units.mul_inv U.det⟩
  let V' : Matrix.SpecialLinearGroup (Fin 3) R :=
    ⟨determinantDiagonal U.det * V.val, by
      rw [Matrix.det_mul, determinantDiagonal_det]
      exact hd⟩
  refine ⟨a, ⟨ha, hs, U', V', ?_⟩, ?_⟩
  · change (g : Matrix (Fin 3) (Fin 3) K) =
      (U.val * determinantDiagonal U.det⁻¹).map (algebraMap R K) *
      Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
      (determinantDiagonal U.det * V.val).map (algebraMap R K)
    rw [Matrix.map_mul, Matrix.map_mul]
    calc
      _ = U.val.map (algebraMap R K) *
          Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
          V.val.map (algebraMap R K) := h
      _ = U.val.map (algebraMap R K) *
          ((determinantDiagonal U.det⁻¹).map (algebraMap R K) *
            Matrix.diagonal (fun i => (algebraMap R K π) ^ a i) *
            (determinantDiagonal U.det).map (algebraMap R K)) *
          V.val.map (algebraMap R K) := by rw [determinantDiagonal_cancel]
      _ = _ := by simp only [mul_assoc]
  · rintro b ⟨hb, _, U'', V'', hb'⟩
    exact huniq b ⟨hb, Matrix.SpecialLinearGroup.toGL U'',
      Matrix.SpecialLinearGroup.toGL V'', hb'⟩

end OAI.Algebra.Modules.ElementaryDivisorsExistenceLinear.Construction
