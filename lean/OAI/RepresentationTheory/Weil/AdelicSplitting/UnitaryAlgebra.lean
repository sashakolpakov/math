import OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryBase

/-! # Unitary Algebra -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryAlgebra.Construction

noncomputable section

section

/-! The open cell `g - 1` invertible generates a rational unitary group.
An explicit infinite family in the norm-one scalar torus avoids the finite
set of eigenvalues of any given matrix. -/

open scoped Classical

section QuadraticField
variable {F : Type*} [Field F] [CharZero F] (d : F)
  [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)]

def cayleyScalar (t : F) : UnitaryBase.Construction.Quadratic F d :=
  (⟨t, 1⟩ : UnitaryBase.Construction.Quadratic F d) / star (⟨t, 1⟩ : UnitaryBase.Construction.Quadratic F d)

omit [Fact (∀ r : F, r ^ 2 ≠ d + 0 * r)] in
theorem cayleyNumerator_ne_zero (t : F) : (⟨t, 1⟩ : UnitaryBase.Construction.Quadratic F d) ≠ 0 := by
  intro h
  have hi := congrArg QuadraticAlgebra.im h
  exact one_ne_zero hi

theorem cayleyScalar_ne_zero (t : F) : cayleyScalar d t ≠ 0 :=
  div_ne_zero (cayleyNumerator_ne_zero d t)
    (star_ne_zero.mpr (cayleyNumerator_ne_zero d t))

theorem cayleyScalar_unitary (t : F) : star (cayleyScalar d t) * cayleyScalar d t = 1 := by
  unfold cayleyScalar
  rw [star_div₀, star_star]
  rw [div_mul_div_cancel₀ (cayleyNumerator_ne_zero d t),
    div_self (star_ne_zero.mpr (cayleyNumerator_ne_zero d t))]

theorem cayleyScalar_injective : Function.Injective (cayleyScalar d) := by
  intro s t h
  have hn (r : F) := star_ne_zero.mpr (cayleyNumerator_ne_zero d r)
  have he := (div_eq_div_iff (hn s) (hn t)).mp h
  have hi := congrArg QuadraticAlgebra.im he
  simp only [QuadraticAlgebra.im_mul, QuadraticAlgebra.re_star,
    QuadraticAlgebra.im_star, mul_neg, mul_one, one_mul, add_zero] at hi
  have htwo : (2 : F) * (s - t) = 0 := by linear_combination -hi
  exact sub_eq_zero.mp ((mul_eq_zero.mp htwo).resolve_left (by norm_num))

end QuadraticField

section ScalarMatrices
variable {E : Type*} [Field E] [StarRing E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def scalarUnitary (H : Matrix ι ι E) (z : Eˣ)
    (hz : star (z : E) * z = 1) : UnitaryBase.Construction.Unitary H := by
  refine ⟨Units.map (Matrix.scalar ι).toMonoidHom z, ?_⟩
  change (Matrix.scalar ι (z : E)).conjTranspose * H * Matrix.scalar ι (z : E) = H
  rw [Matrix.scalar_apply, Matrix.diagonal_conjTranspose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change star (z : E) * H i j * z = H i j
  calc
    star (z : E) * H i j * z = (star (z : E) * z) * H i j := by ring
    _ = H i j := by rw [hz, one_mul]

theorem scalarUnitary_open (H : Matrix ι ι E) (z : Eˣ)
    (hz : star (z : E) * z = 1) (hne : (z : E) ≠ 1) :
    IsUnit ((scalarUnitary H z hz).val.val - 1) := by
  change IsUnit (Matrix.scalar ι (z : E) - 1)
  rw [← map_one (Matrix.scalar ι), ← map_sub]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hne)).map (Matrix.scalar ι)

theorem unitary_open_factorization
    (H : Matrix ι ι E) (g : UnitaryBase.Construction.Unitary H)
    (hzs : Set.Infinite {z : E | star z * z = 1}) :
    ∃ a b : UnitaryBase.Construction.Unitary H, g = a * b ∧
      IsUnit (a.val.val - 1) ∧ IsUnit (b.val.val - 1) := by
  have hp : g.val.val.charpoly ≠ 0 := Matrix.charpoly_monic _ |>.ne_zero
  have hf : Set.Finite ({z : E | Polynomial.IsRoot g.val.val.charpoly z} ∪ {1}) :=
    (Polynomial.finite_setOfPred_isRoot hp).union (Set.finite_singleton 1)
  obtain ⟨z, hz, havoid⟩ := hzs.exists_notMem_finite hf
  have hne : z ≠ 1 := fun h => havoid (Or.inr h)
  have hz0 : z ≠ 0 := by
    intro h
    simp [h] at hz
  let u : Eˣ := Units.mk0 z hz0
  let b := scalarUnitary H u hz
  refine ⟨g * b⁻¹, b, by simp, ?_, scalarUnitary_open H u hz hne⟩
  have he : (Matrix.scalar ι z - g.val.val).det ≠ 0 := by
    rw [← Matrix.eval_charpoly]
    exact fun h => havoid (Or.inl h)
  have hu : IsUnit (g.val.val - b.val.val) := by
    have h := (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr he)
    change IsUnit (g.val.val - Matrix.scalar ι z)
    simpa only [neg_sub] using h.neg
  have heq : (g * b⁻¹).val.val - 1 = (g.val.val - b.val.val) * (b⁻¹).val.val := by
    change g.val.val * (b⁻¹).val.val - 1 = _
    rw [sub_mul]
    have hb : b.val.val * (b⁻¹).val.val = 1 := b.val.val_inv
    rw [hb]
  rw [heq]
  exact hu.mul (b⁻¹).val.isUnit

end ScalarMatrices

theorem rational_unitary_open_factorization
    {F : Type*} [Field F] [CharZero F] (d : F) (hd : ¬ IsSquare d)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι (UnitaryBase.Construction.Quadratic F d)) (g : UnitaryBase.Construction.Unitary H) :
    ∃ a b : UnitaryBase.Construction.Unitary H, g = a * b ∧
      IsUnit (a.val.val - 1) ∧ IsUnit (b.val.val - 1) := by
  let : Fact (∀ r : F, r ^ 2 ≠ d + 0 * r) := ⟨by
    intro r hr
    apply hd
    refine ⟨r, ?_⟩
    simpa [sq] using hr.symm⟩
  apply unitary_open_factorization
  have h : Set.Infinite (Set.range (cayleyScalar d)) :=
    Set.infinite_range_of_injective (cayleyScalar_injective d)
  apply h.mono
  rintro _ ⟨t, rfl⟩
  exact cayleyScalar_unitary d t

end

section

/-! Algebra generated by unitary matrices. The finite-dimensional inverse
lemma supports the Cayley construction without an analytic limiting argument. -/

open scoped Classical

theorem subalgebra_unit_inverse_mem
    {F A : Type*} [Field F] [Ring A] [Algebra F A] [FiniteDimensional F A]
    (S : Subalgebra F A) (u : Aˣ) (hu : (u : A) ∈ S) : ((u⁻¹ : Aˣ) : A) ∈ S := by
  let a : S := ⟨u, hu⟩
  let L : S →ₗ[F] S := LinearMap.mulLeft F a
  have hi : Function.Injective L := by
    intro x y h
    apply Subtype.ext
    have h' : (u : A) * (x : A) = (u : A) * (y : A) := congrArg Subtype.val h
    have h'' := congrArg (fun z : A => ((u⁻¹ : Aˣ) : A) * z) h'
    simpa only [← mul_assoc, Units.inv_mul, one_mul] using h''
  obtain ⟨v, hv⟩ := LinearMap.surjective_of_injective hi (1 : S)
  have he : (u : A) * (v : A) = 1 := congrArg Subtype.val hv
  have hv' : (v : A) = ((u⁻¹ : Aˣ) : A) := by
    have h := congrArg (fun z : A => ((u⁻¹ : Aˣ) : A) * z) he
    simpa only [← mul_assoc, Units.inv_mul, one_mul, mul_one] using h
  exact hv' ▸ v.property

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [StarRing E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Equal Gram matrices give a unitary quotient. -/
def unitaryOfGramEquality (H : Matrix ι ι E)
    (u v : (Matrix ι ι E)ˣ)
    (h : (u : Matrix ι ι E).conjTranspose * H * u =
      (v : Matrix ι ι E).conjTranspose * H * v) : UnitaryBase.Construction.Unitary H := by
  refine ⟨u * v⁻¹, ?_⟩
  change ((u : Matrix ι ι E) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E)).conjTranspose * H *
    ((u : Matrix ι ι E) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E)) = H
  rw [Matrix.conjTranspose_mul]
  calc
    _ = ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E).conjTranspose *
        ((u : Matrix ι ι E).conjTranspose * H * u) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
      simp only [mul_assoc]
    _ = _ := by
      rw [h]
      have hv : ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E).conjTranspose *
          (v : Matrix ι ι E).conjTranspose = 1 := by
        rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
      calc
        _ = (((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E).conjTranspose *
            (v : Matrix ι ι E).conjTranspose) * H *
            ((v : Matrix ι ι E) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E)) := by
          simp only [mul_assoc]
        _ = H := by rw [hv, Units.mul_inv, one_mul, mul_one]

theorem cayley_gram_equality (H A : Matrix ι ι E) (s : E) (hs : star s = s)
    (hA : A.conjTranspose * H = -(H * A)) :
    (Matrix.scalar ι s + A).conjTranspose * H * (Matrix.scalar ι s + A) =
      (Matrix.scalar ι s - A).conjTranspose * H * (Matrix.scalar ι s - A) := by
  have hscalar : (Matrix.scalar ι s).conjTranspose = Matrix.scalar ι s := by
    simp [Matrix.scalar_apply, Matrix.diagonal_conjTranspose, hs]
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub, hscalar]
  simp only [add_mul, mul_add, sub_mul, mul_sub, hA, neg_mul]
  have hc : Matrix.scalar ι s * H * A = H * A * Matrix.scalar ι s := by
    simpa only [mul_assoc] using! (Algebra.commutes s (H * A))
  rw [hc]
  abel

end

section

/-! Cayley transforms place every infinitesimal unitary matrix in the
finite-dimensional algebra generated by the actual unitary group. -/

open scoped Classical

section Scalars
variable {F E : Type*} [Field F] [Infinite F] [Field E] [Algebra F E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_scalar_units_add_sub (A : Matrix ι ι E) :
    ∃ s : F, s ≠ 0 ∧ IsUnit (algebraMap F (Matrix ι ι E) s + A) ∧
      IsUnit (algebraMap F (Matrix ι ι E) s - A) := by
  have hi : Set.Infinite (Set.range (algebraMap F E)) :=
    Set.infinite_range_of_injective (algebraMap F E).injective
  have hf : Set.Finite ({z : E | Polynomial.IsRoot A.charpoly z} ∪
      {z : E | Polynomial.IsRoot (-A).charpoly z} ∪ {0}) :=
    ((Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic A).ne_zero).union
      (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic (-A)).ne_zero)).union
      (Set.finite_singleton 0)
  obtain ⟨z, ⟨s, rfl⟩, hz⟩ := hi.exists_notMem_finite hf
  have hs : s ≠ 0 := by
    intro hs
    apply hz
    exact Or.inr (by simp [hs])
  have hminus : IsUnit (Matrix.scalar ι (algebraMap F E s) - A) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [← Matrix.eval_charpoly]
    exact fun h => hz (Or.inl (Or.inl h))
  have hplus : IsUnit (Matrix.scalar ι (algebraMap F E s) - (-A)) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    rw [← Matrix.eval_charpoly]
    exact fun h => hz (Or.inl (Or.inr h))
  refine ⟨s, hs, ?_, hminus⟩
  simpa only [sub_neg_eq_add] using! hplus

end Scalars

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [StarRing E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem subalgebra_contains_skew_adjoint
    (hF : ∀ s : F, star (algebraMap F E s) = algebraMap F E s)
    (H A : Matrix ι ι E) (hA : A.conjTranspose * H = -(H * A))
    (S : Subalgebra F (Matrix ι ι E))
    (hS : ∀ g : UnitaryBase.Construction.Unitary H, g.val.val ∈ S) : A ∈ S := by
  obtain ⟨s, hs, ⟨u, hu⟩, ⟨v, hv⟩⟩ := exists_scalar_units_add_sub (F := F) A
  let q : Matrix ι ι E := algebraMap F (Matrix ι ι E) s
  have hGram : (u : Matrix ι ι E).conjTranspose * H * u =
      (v : Matrix ι ι E).conjTranspose * H * v := by
    rw [hu, hv]
    exact cayley_gram_equality H A (algebraMap F E s) (hF s) hA
  let g := unitaryOfGramEquality H u v hGram
  have hg : g.val.val = (u : Matrix ι ι E) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := rfl
  have hplus : g.val.val + 1 = (q + q) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
    calc
      _ = ((u : Matrix ι ι E) + v) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
        rw [add_mul, Units.mul_inv, hg]
      _ = _ := by rw [hu, hv]; congr 1; dsimp only [q]; abel
  have hminus : g.val.val - 1 = (A + A) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
    calc
      _ = ((u : Matrix ι ι E) - v) * ((v⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
        rw [sub_mul, Units.mul_inv, hg]
      _ = _ := by rw [hu, hv]; congr 1; abel
  have hsum : s + s ≠ 0 := by
    rw [← two_mul]
    exact mul_ne_zero (by norm_num) hs
  have hunit : IsUnit (g.val.val + 1) := by
    rw [hplus]
    have hq : IsUnit (q + q) := by
      change IsUnit (algebraMap F (Matrix ι ι E) s + algebraMap F (Matrix ι ι E) s)
      rw [← map_add]
      exact (isUnit_iff_ne_zero.mpr hsum).map (algebraMap F (Matrix ι ι E))
    exact hq.mul (v⁻¹).isUnit
  obtain ⟨w, hw⟩ := hunit
  have hwmem : (w : Matrix ι ι E) ∈ S := hw ▸ S.add_mem (hS g) S.one_mem
  have hwinv := subalgebra_unit_inverse_mem S w hwmem
  have hrel : A * (g.val.val + 1) = q * (g.val.val - 1) := by
    rw [hplus, hminus, ← mul_assoc, ← mul_assoc]
    congr 1
    have hqA : A * q = q * A := (Algebra.commutes s A).symm
    simp only [mul_add, hqA]
  have hEq : A = (q * (g.val.val - 1)) * ((w⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
    calc
      _ = (A * (w : Matrix ι ι E)) * ((w⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by
        rw [mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [hw, hrel]
  rw [hEq]
  exact S.mul_mem (S.mul_mem (S.algebraMap_mem s) (S.sub_mem (hS g) S.one_mem)) hwinv

end

section

/-! A nondegenerate Hermitian unitary group generates the full matrix
algebra over a characteristic-zero fixed subfield. -/

open scoped Classical

section Adjoint
variable {E : Type*} [Field E] [StarRing E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem hermitian_unit_inverse (H : (Matrix ι ι E)ˣ)
    (hH : (H : Matrix ι ι E).conjTranspose = H) :
    ((H⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E).conjTranspose = H⁻¹ := by
  have h : ((H⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E).conjTranspose * (H : Matrix ι ι E) = 1 := by
    rw [← hH, ← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  calc
    _ = (((H⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E).conjTranspose * (H : Matrix ι ι E)) *
        ((H⁻¹ : (Matrix ι ι E)ˣ) : Matrix ι ι E) := by rw [mul_assoc, Units.mul_inv, mul_one]
    _ = _ := by rw [h, one_mul]

def matrixFormAdjoint (H : (Matrix ι ι E)ˣ) (A : Matrix ι ι E) : Matrix ι ι E :=
  (H⁻¹ : (Matrix ι ι E)ˣ) * A.conjTranspose * H

theorem matrixFormAdjoint_left (H : (Matrix ι ι E)ˣ) (A : Matrix ι ι E) :
    (H : Matrix ι ι E) * matrixFormAdjoint H A = A.conjTranspose * H := by
  rw [matrixFormAdjoint, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

theorem matrixFormAdjoint_right (H : (Matrix ι ι E)ˣ)
    (hH : (H : Matrix ι ι E).conjTranspose = H) (A : Matrix ι ι E) :
    (matrixFormAdjoint H A).conjTranspose * H = (H : Matrix ι ι E) * A := by
  rw [matrixFormAdjoint, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hH, hermitian_unit_inverse H hH, Matrix.conjTranspose_conjTranspose]
  rw [mul_assoc, mul_assoc, Units.inv_mul, mul_one]

theorem matrix_sub_formAdjoint_skew (H : (Matrix ι ι E)ˣ)
    (hH : (H : Matrix ι ι E).conjTranspose = H) (A : Matrix ι ι E) :
    (A - matrixFormAdjoint H A).conjTranspose * H =
      -((H : Matrix ι ι E) * (A - matrixFormAdjoint H A)) := by
  rw [Matrix.conjTranspose_sub, sub_mul, matrixFormAdjoint_right H hH,
    mul_sub, matrixFormAdjoint_left]
  abel

theorem imaginary_matrix_add_formAdjoint_skew (H : (Matrix ι ι E)ˣ)
    (hH : (H : Matrix ι ι E).conjTranspose = H) (A : Matrix ι ι E)
    (δ : E) (hδ : star δ = -δ) :
    (δ • (A + matrixFormAdjoint H A)).conjTranspose * H =
      -((H : Matrix ι ι E) * (δ • (A + matrixFormAdjoint H A))) := by
  rw [Matrix.conjTranspose_smul, hδ, Matrix.conjTranspose_add,
    smul_mul_assoc, add_mul, matrixFormAdjoint_right H hH,
    mul_smul_comm, mul_add, matrixFormAdjoint_left]
  simp only [neg_smul]
  congr 2
  exact add_comm _ _

end Adjoint

variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [StarRing E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem unitary_subalgebra_eq_top
    (hF : ∀ s : F, star (algebraMap F E s) = algebraMap F E s)
    (δ : E) (hδ : star δ = -δ) (hδ0 : δ ≠ 0)
    (H : (Matrix ι ι E)ˣ) (hH : (H : Matrix ι ι E).conjTranspose = H)
    (S : Subalgebra F (Matrix ι ι E))
    (hS : ∀ g : UnitaryBase.Construction.Unitary (H : Matrix ι ι E), g.val.val ∈ S) : S = ⊤ := by
  have hskew (A : Matrix ι ι E) (hA : A.conjTranspose * H = -((H : Matrix ι ι E) * A)) : A ∈ S :=
    subalgebra_contains_skew_adjoint (F := F) (E := E) hF (H : Matrix ι ι E) A hA S hS
  have hδmem : Matrix.scalar ι δ ∈ S := by
    apply hskew
    have hstar : (Matrix.scalar ι δ).conjTranspose = -(Matrix.scalar ι δ) := by
      simp [Matrix.scalar_apply, Matrix.diagonal_conjTranspose, hδ]
    rw [hstar, neg_mul]
    congr 1
    exact (Algebra.commutes δ (H : Matrix ι ι E))
  let u : (Matrix ι ι E)ˣ := Units.map (Matrix.scalar ι).toMonoidHom (Units.mk0 δ hδ0)
  have hu : (u : Matrix ι ι E) ∈ S := hδmem
  have hδinv : Matrix.scalar ι δ⁻¹ ∈ S := subalgebra_unit_inverse_mem S u hu
  apply top_unique
  intro A _
  have ha := hskew (A - matrixFormAdjoint H A) (matrix_sub_formAdjoint_skew H hH A)
  have hb := hskew (δ • (A + matrixFormAdjoint H A))
    (imaginary_matrix_add_formAdjoint_skew H hH A δ hδ)
  have hb' : A + matrixFormAdjoint H A ∈ S := by
    have h := S.mul_mem hδinv hb
    have he : Matrix.scalar ι δ⁻¹ * (δ • (A + matrixFormAdjoint H A)) =
        A + matrixFormAdjoint H A := by
      change (algebraMap E (Matrix ι ι E) δ⁻¹) * (δ • (A + matrixFormAdjoint H A)) = _
      rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
    rwa [he] at h
  have hsum : A + A ∈ S := by
    have h := S.add_mem ha hb'
    convert h using 1; abel
  have h := S.smul_mem hsum (2 : F)⁻¹
  rw [← two_smul F A, smul_smul, inv_mul_cancel₀ (by norm_num : (2 : F) ≠ 0), one_smul] at h
  exact h

theorem skew_unitary_subalgebra_eq_top
    (hF : ∀ s : F, star (algebraMap F E s) = algebraMap F E s)
    (δ : E) (hδ : star δ = -δ) (hδ0 : δ ≠ 0)
    (K : (Matrix ι ι E)ˣ) (hK : (K : Matrix ι ι E).conjTranspose = -K)
    (S : Subalgebra F (Matrix ι ι E))
    (hS : ∀ g : UnitaryBase.Construction.Unitary (K : Matrix ι ι E), g.val.val ∈ S) : S = ⊤ := by
  let u : (Matrix ι ι E)ˣ := Units.map (Matrix.scalar ι).toMonoidHom (Units.mk0 δ hδ0)
  let H : (Matrix ι ι E)ˣ := u * K
  have hval : (H : Matrix ι ι E) = δ • (K : Matrix ι ι E) := by
    change Matrix.scalar ι δ * (K : Matrix ι ι E) = δ • (K : Matrix ι ι E)
    exact (Algebra.smul_def δ (K : Matrix ι ι E)).symm
  have hH : (H : Matrix ι ι E).conjTranspose = H := by
    rw [hval, Matrix.conjTranspose_smul, hδ, hK]
    simp
  apply unitary_subalgebra_eq_top hF δ hδ hδ0 H hH S
  intro g
  have hg : g.val.val.conjTranspose * (K : Matrix ι ι E) * g.val.val = K := by
    have h := g.property
    change g.val.val.conjTranspose * (H : Matrix ι ι E) * g.val.val = H at h
    simpa only [hval, mul_smul_comm, smul_mul_assoc, smul_right_inj hδ0] using h
  exact hS ⟨g.val, hg⟩

end

/-! Algebraic irreducibility of the tensor representation of the full
unitary pair, obtained from its two matrix algebras. -/

open scoped Classical Kronecker

section Tensor
variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def matrixTensorFirst : Matrix I I E →ₐ[F] Matrix (I × J) (I × J) E where
  toFun A := A ⊗ₖ (1 : Matrix J J E)
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.zero_kronecker _
  map_add' A B := Matrix.add_kronecker A B _
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  commutes' s := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker, Matrix.one_kronecker_one]

def matrixTensorSecond : Matrix J J E →ₐ[F] Matrix (I × J) (I × J) E where
  toFun A := (1 : Matrix I I E) ⊗ₖ A
  map_one' := Matrix.one_kronecker_one
  map_zero' := Matrix.kronecker_zero _
  map_add' A B := Matrix.kronecker_add _ A B
  map_mul' A B := by rw [← Matrix.mul_kronecker_mul, one_mul]
  commutes' s := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem matrix_subalgebra_eq_top_of_tensor_factors
    (S : Subalgebra F (Matrix (I × J) (I × J) E))
    (h₁ : ∀ A : Matrix I I E, A ⊗ₖ (1 : Matrix J J E) ∈ S)
    (h₂ : ∀ B : Matrix J J E, (1 : Matrix I I E) ⊗ₖ B ∈ S) : S = ⊤ := by
  have ht (A : Matrix I I E) (B : Matrix J J E) : A ⊗ₖ B ∈ S := by
    have h := S.mul_mem (h₁ A) (h₂ B)
    simpa only [← Matrix.mul_kronecker_mul, mul_one, one_mul] using h
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply S.sum_mem
  rintro ⟨i, j⟩ _
  apply S.sum_mem
  rintro ⟨i', j'⟩ _
  have h := ht (Matrix.single i i' (M (i, j) (i', j'))) (Matrix.single j j' 1)
  simpa only [Matrix.single_kronecker_single, mul_one] using h

end Tensor

section UnitaryTensor
variable {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [StarRing E]
  {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

theorem unitary_tensor_subalgebra_eq_top
    (hF : ∀ s : F, star (algebraMap F E s) = algebraMap F E s)
    (δ : E) (hδ : star δ = -δ) (hδ0 : δ ≠ 0)
    (H : (Matrix I I E)ˣ) (hH : (H : Matrix I I E).conjTranspose = H)
    (K : (Matrix J J E)ˣ) (hK : (K : Matrix J J E).conjTranspose = -K)
    (S : Subalgebra F (Matrix (I × J) (I × J) E))
    (hS : ∀ g : UnitaryBase.Construction.Unitary (H : Matrix I I E) × UnitaryBase.Construction.Unitary (K : Matrix J J E),
      g.1.val.val ⊗ₖ g.2.val.val ∈ S) : S = ⊤ := by
  have h₁ : S.comap (matrixTensorFirst (F := F) (E := E) (I := I) (J := J)) = ⊤ := by
    apply unitary_subalgebra_eq_top hF δ hδ hδ0 H hH
    intro g
    exact hS (g, 1)
  have h₂ : S.comap (matrixTensorSecond (F := F) (E := E) (I := I) (J := J)) = ⊤ := by
    apply skew_unitary_subalgebra_eq_top hF δ hδ hδ0 K hK
    intro g
    exact hS (1, g)
  apply matrix_subalgebra_eq_top_of_tensor_factors S
  · intro A
    exact show A ∈ S.comap matrixTensorFirst from h₁ ▸ (show A ∈ (⊤ : Subalgebra F (Matrix I I E)) from trivial)
  · intro B
    exact show B ∈ S.comap matrixTensorSecond from h₂ ▸ (show B ∈ (⊤ : Subalgebra F (Matrix J J E)) from trivial)

end UnitaryTensor

variable {F E : Type*} [Field F] [Field E] [Algebra F E]
  {I : Type*} [Fintype I] [DecidableEq I]

def matrixSubmoduleStabilizer (L : Submodule F (I → E)) : Subalgebra F (Matrix I I E) where
  carrier := {A | ∀ x ∈ L, A.mulVec x ∈ L}
  zero_mem' := by intro x _; simp
  one_mem' := by intro x hx; simpa using hx
  add_mem' := by intro A B hA hB x hx; simpa only [Matrix.add_mulVec] using L.add_mem (hA x hx) (hB x hx)
  mul_mem' := by intro A B hA hB x hx; simpa only [Matrix.mulVec_mulVec] using hA (B.mulVec x) (hB x hx)
  algebraMap_mem' s := by
    intro x hx
    simpa only [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec] using L.smul_mem s hx

theorem eq_bot_or_top_of_matrix_stabilizer_top (L : Submodule F (I → E))
    (hL : matrixSubmoduleStabilizer L = ⊤) : L = ⊥ ∨ L = ⊤ := by
  by_cases hzero : L = ⊥
  · exact Or.inl hzero
  right
  have hex : ∃ x ∈ L, x ≠ 0 := by
    by_contra! h
    apply hzero
    apply bot_unique
    intro x hx
    exact h x hx
  obtain ⟨x, hx, hxn⟩ := hex
  have hi : ∃ i, x i ≠ 0 := by
    by_contra! h
    exact hxn (funext h)
  obtain ⟨i, hi⟩ := hi
  apply top_unique
  intro y _
  let A : Matrix I I E := fun j k => if k = i then y j * (x i)⁻¹ else 0
  have hA : A ∈ matrixSubmoduleStabilizer L := hL ▸ (show A ∈ (⊤ : Subalgebra F (Matrix I I E)) from trivial)
  have he : A.mulVec x = y := by
    ext j
    simp [A, Matrix.mulVec, dotProduct, hi]
  simpa only [he] using hA x hx

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.UnitaryAlgebra.Construction
