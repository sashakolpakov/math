import OAI.RepresentationTheory.Weil.UnitarySplitting.CayleyProduct
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticNorm

/-! # Tensor Unitary -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary.Construction

noncomputable section

section

/-! Determinant identities and character invariance in the generic splitting
factor. These identities concern the actual unitary matrices. -/

open _root_.Matrix

def matrixDetUnit {E I : Type} [CommRing E] [Fintype I] [DecidableEq I]
    (u : (Matrix I I E)ˣ) : Eˣ := Units.map Matrix.detMonoidHom u

theorem matrixDetUnit_mul {E I : Type} [CommRing E] [Fintype I] [DecidableEq I]
    (u v : (Matrix I I E)ˣ) : matrixDetUnit (u * v) = matrixDetUnit u * matrixDetUnit v :=
  (Units.map (Matrix.detMonoidHom : Matrix I I E →* E)).map_mul u v

section Characters

variable {F E : Type} [NormedField F] [NormedField E] [Algebra F E]
variable [FiniteDimensional F E] [CharZero F]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (hQuadratic : Module.finrank F E = 2) (σ : E ≃ₐ[F] E)
variable (hne : ∃ z : E, σ z ≠ z)
variable (ω : Fˣ →ₜ* Circle) (hω : UnitarySplitting.Characters.Construction.IsExtensionQuadraticCharacter (E := E) ω)
variable {d : ℕ} (χ : Eˣ →ₜ* Circle) (hχ : UnitarySplitting.Characters.Construction.HasSplittingRestriction ω d χ)

include hQuadratic hne hω hχ in
theorem splittingCharacter_congruence (u r : (Matrix I I E)ˣ) :
    χ (matrixDetUnit (TracePairing.Construction.adjointMatrixUnit σ u * r * u)) = χ (matrixDetUnit r) := by
  have hadj : matrixDetUnit (TracePairing.Construction.adjointMatrixUnit σ u) =
      Units.map σ.toMonoidHom (matrixDetUnit u) := by
    apply Units.ext
    exact TracePairing.Construction.adjointMatrix_det σ (u : Matrix I I E)
  rw [matrixDetUnit_mul, matrixDetUnit_mul, hadj, map_mul, map_mul]
  calc
    _ = (χ (Units.map σ.toMonoidHom (matrixDetUnit u)) * χ (matrixDetUnit u)) *
        χ (matrixDetUnit r) := by ac_rfl
    _ = χ (matrixDetUnit r) := by
      rw [QuadraticNorm.Construction.splittingCharacter_conjugate ω hω χ hχ hQuadratic σ hne, one_mul]

end Characters

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {I : Type} [Fintype I] [DecidableEq I]
variable (σ : E ≃ₐ[F] E) (Q : Matrix I I E)

theorem unitaryDifferenceForm_det (g : DualPair.Construction.unitaryGroup σ Q) :
    (TracePairing.Construction.unitaryDifferenceForm σ Q g).det = Q.det * ((g.val : Matrix I I E) - 1).det :=
  Matrix.det_mul _ _

theorem unitaryProductForm_discriminant (g h : DualPair.Construction.unitaryGroup σ Q)
    (hgh : g * h ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) :
    (CayleyProduct.Construction.unitaryProductForm σ Q g h).det * (TracePairing.Construction.unitaryDifferenceForm σ Q (g * h)).det =
      (TracePairing.Construction.unitaryDifferenceForm σ Q g).det * (TracePairing.Construction.unitaryDifferenceForm σ Q h).det := by
  rw [CayleyProduct.Construction.unitaryProductForm_det, unitaryDifferenceForm_det, unitaryDifferenceForm_det,
    unitaryDifferenceForm_det]
  calc
    _ = Q.det * Q.det * ((g.val : Matrix I I E) - 1).det * ((h.val : Matrix I I E) - 1).det *
        ((((g * h).val : Matrix I I E) - 1).det⁻¹ * (((g * h).val : Matrix I I E) - 1).det) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hgh]; ring

theorem unitaryProductForm_det_in_base [FiniteDimensional F E] [CharZero F]
    (hQuadratic : Module.finrank F E = 2) (hne : ∃ z : E, σ z ≠ z)
    (hQ : Q.det ≠ 0) (hskew : DualPair.Construction.adjointMatrix σ Q = -Q) (g h : DualPair.Construction.unitaryGroup σ Q)
    (hg : g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) (hh : h ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q)
    (hgh : g * h ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) :
    ∃ a : Fˣ, algebraMap F E (a : F) = (CayleyProduct.Construction.unitaryProductForm σ Q g h).det := by
  have hherm := CayleyProduct.Construction.unitaryProductForm_hermitian σ (TracePairing.Construction.quadratic_automorphism_involutive hQuadratic σ)
    Q hQ hskew g h hg hh hgh
  have hfixed : σ (CayleyProduct.Construction.unitaryProductForm σ Q g h).det = (CayleyProduct.Construction.unitaryProductForm σ Q g h).det := by
    rw [← TracePairing.Construction.adjointMatrix_det σ, hherm]
  obtain ⟨a, ha⟩ := (QuadraticNorm.Construction.quadratic_fixed_iff hQuadratic σ hne _).mp hfixed
  have hane : a ≠ 0 := by
    intro hzero
    have hz := CayleyProduct.Construction.unitaryProductForm_nondegenerate σ Q hQ g h hg hh hgh
    apply hz
    rw [← ha, hzero, map_zero]
  exact ⟨Units.mk0 a hane, ha⟩

end

section

/-! Reindexing unitary matrices preserves generic domains and their
difference and product forms. -/

open _root_.Matrix

theorem matrixReindex_mul
    {E I J : Type} [Field E] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (A B : Matrix I I E) :
    Matrix.reindex e e (A * B) = Matrix.reindex e e A * Matrix.reindex e e B :=
  map_mul (Matrix.reindexRingEquiv E e) A B

variable {F E I J : Type} [Field F] [Field E] [Algebra F E]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (σ : E ≃ₐ[F] E) (e : I ≃ J)

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] in
theorem adjointMatrix_reindex (A : Matrix I I E) :
    DualPair.Construction.adjointMatrix σ (Matrix.reindex e e A) = Matrix.reindex e e (DualPair.Construction.adjointMatrix σ A) := rfl

def unitaryReindex (Q : Matrix I I E) : DualPair.Construction.unitaryGroup σ Q →* DualPair.Construction.unitaryGroup σ (Matrix.reindex e e Q) where
  toFun g := ⟨Units.map (Matrix.reindexRingEquiv E e).toMonoidHom g.val, by
    change DualPair.Construction.adjointMatrix σ (Matrix.reindex e e (g.val : Matrix I I E)) * Matrix.reindex e e Q *
      Matrix.reindex e e (g.val : Matrix I I E) = Matrix.reindex e e Q
    rw [adjointMatrix_reindex, ← matrixReindex_mul e, ← matrixReindex_mul e, g.property]⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (Units.map (Matrix.reindexRingEquiv E e).toMonoidHom)
  map_mul' g h := by
    apply Subtype.ext
    exact map_mul (Units.map (Matrix.reindexRingEquiv E e).toMonoidHom) g.val h.val

theorem unitaryReindex_matrix (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) :
    ((unitaryReindex σ e Q g).val : Matrix J J E) = Matrix.reindex e e (g.val : Matrix I I E) := rfl

theorem unitaryReindex_difference (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) :
    ((unitaryReindex σ e Q g).val : Matrix J J E) - 1 =
      Matrix.reindex e e ((g.val : Matrix I I E) - 1) := by
  change Matrix.reindexRingEquiv E e (g.val : Matrix I I E) - 1 =
    Matrix.reindexRingEquiv E e ((g.val : Matrix I I E) - 1)
  rw [map_sub, map_one]

theorem unitaryReindex_generic (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) :
    unitaryReindex σ e Q g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ (Matrix.reindex e e Q) ↔
      g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q := by
  change (((unitaryReindex σ e Q g).val : Matrix J J E) - 1).det ≠ 0 ↔ _
  rw [unitaryReindex_difference, Matrix.det_reindex_self]
  rfl

theorem unitaryDifferenceForm_reindex (Q : Matrix I I E) (g : DualPair.Construction.unitaryGroup σ Q) :
    TracePairing.Construction.unitaryDifferenceForm σ (Matrix.reindex e e Q) (unitaryReindex σ e Q g) =
      Matrix.reindex e e (TracePairing.Construction.unitaryDifferenceForm σ Q g) := by
  rw [TracePairing.Construction.unitaryDifferenceForm, unitaryReindex_difference, ← matrixReindex_mul e]
  rfl

theorem unitaryProductForm_reindex (Q : Matrix I I E) (g h : DualPair.Construction.unitaryGroup σ Q) :
    CayleyProduct.Construction.unitaryProductForm σ (Matrix.reindex e e Q) (unitaryReindex σ e Q g) (unitaryReindex σ e Q h) =
      Matrix.reindex e e (CayleyProduct.Construction.unitaryProductForm σ Q g h) := by
  unfold CayleyProduct.Construction.unitaryProductForm
  rw [← map_mul, unitaryReindex_difference, unitaryReindex_difference,
    unitaryReindex_difference, Matrix.inv_reindex,
    ← matrixReindex_mul e, ← matrixReindex_mul e, ← matrixReindex_mul e]

end

section

/-! The generic unitary product form for a tensor multiplicity is the
tensor product of the original product form with the multiplicity form. -/

open _root_.Matrix
open scoped Kronecker

theorem matrixKronecker_sub_left {E I J : Type} [Ring E]
    (A B : Matrix I I E) (C : Matrix J J E) : (A - B) ⊗ₖ C = A ⊗ₖ C - B ⊗ₖ C := by
  ext i j
  exact sub_mul _ _ _

theorem matrixKronecker_neg_left {E I J : Type} [Ring E]
    (A : Matrix I I E) (C : Matrix J J E) : (-A) ⊗ₖ C = -(A ⊗ₖ C) := by
  ext i j
  exact neg_mul _ _

variable {F E I J : Type} [Field F] [Field E] [Algebra F E]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable (σ : E ≃ₐ[F] E) (Q : Matrix I I E) (W : Matrix J J E)

def leftTensorUnitary : DualPair.Construction.unitaryGroup σ Q →* DualPair.Construction.unitaryGroup σ (Q ⊗ₖ W) :=
  (DualPair.Construction.tensorUnitaryAction σ Q W).comp ((MonoidHom.id _).prod 1)

theorem leftTensorUnitary_matrix (g : DualPair.Construction.unitaryGroup σ Q) :
    ((leftTensorUnitary σ Q W g).val : Matrix (I × J) (I × J) E) =
      (g.val : Matrix I I E) ⊗ₖ (1 : Matrix J J E) := rfl

theorem leftTensorUnitary_difference (g : DualPair.Construction.unitaryGroup σ Q) :
    ((leftTensorUnitary σ Q W g).val : Matrix (I × J) (I × J) E) - 1 =
      ((g.val : Matrix I I E) - 1) ⊗ₖ (1 : Matrix J J E) := by
  rw [leftTensorUnitary_matrix, matrixKronecker_sub_left, Matrix.one_kronecker_one]

theorem leftTensorUnitary_generic (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) :
    leftTensorUnitary σ Q W g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ (Q ⊗ₖ W) := by
  change (((leftTensorUnitary σ Q W g).val : Matrix (I × J) (I × J) E) - 1).det ≠ 0
  rw [leftTensorUnitary_difference, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]
  exact pow_ne_zero _ hg

omit σ Q W in
theorem kronecker_one_nonsing_inv (A : Matrix I I E) (hA : A.det ≠ 0) :
    (A ⊗ₖ (1 : Matrix J J E))⁻¹ = A⁻¹ ⊗ₖ (1 : Matrix J J E) := by
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.mul_kronecker_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA),
    one_mul, Matrix.one_kronecker_one]

theorem leftTensorUnitary_productForm (g h : DualPair.Construction.unitaryGroup σ Q)
    (hgh : g * h ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) :
    CayleyProduct.Construction.unitaryProductForm σ (Q ⊗ₖ W) (leftTensorUnitary σ Q W g) (leftTensorUnitary σ Q W h) =
      CayleyProduct.Construction.unitaryProductForm σ Q g h ⊗ₖ W := by
  unfold CayleyProduct.Construction.unitaryProductForm
  rw [← map_mul, leftTensorUnitary_difference, leftTensorUnitary_difference, leftTensorUnitary_difference,
    kronecker_one_nonsing_inv _ hgh, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [mul_one]

theorem leftTensorUnitary_productForm_det (g h : DualPair.Construction.unitaryGroup σ Q)
    (hgh : g * h ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) :
    (CayleyProduct.Construction.unitaryProductForm σ (Q ⊗ₖ W) (leftTensorUnitary σ Q W g) (leftTensorUnitary σ Q W h)).det =
      (CayleyProduct.Construction.unitaryProductForm σ Q g h).det ^ Fintype.card J * W.det ^ Fintype.card I := by
  rw [leftTensorUnitary_productForm σ Q W g h hgh, Matrix.det_kronecker]

end

/-! A unitary action with arbitrary finite multiplicity and nonzero base
field weights, indexed by the concrete oscillator dimension. -/

open _root_.Matrix
open scoped BigOperators Kronecker

variable {F E : Type} [Field F] [Field E] [Algebra F E] {m n : ℕ}

def multiplicityForm (a : Fin n → Fˣ) : Matrix (Fin n) (Fin n) E :=
  Matrix.diagonal (fun i => algebraMap F E (a i : F))

theorem multiplicityForm_det (a : Fin n → Fˣ) :
    (multiplicityForm (E := E) a).det = algebraMap F E ((∏ i, a i : Fˣ) : F) := by
  rw [multiplicityForm, Matrix.det_diagonal, Units.coe_prod, map_prod]

theorem multiplicityForm_nondegenerate (a : Fin n → Fˣ) : (multiplicityForm (E := E) a).det ≠ 0 := by
  rw [multiplicityForm_det]
  exact (map_ne_zero (algebraMap F E)).mpr (Units.ne_zero _)

theorem multiplicityForm_hermitian (σ : E ≃ₐ[F] E) (a : Fin n → Fˣ) :
    DualPair.Construction.adjointMatrix σ (multiplicityForm a) = multiplicityForm a := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [multiplicityForm, DualPair.Construction.adjointMatrix, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply, ite_true, σ.commutes]
  · simp only [multiplicityForm, DualPair.Construction.adjointMatrix, Matrix.transpose_apply, Matrix.map_apply,
      Matrix.diagonal_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij), map_zero]

def weightedTensorForm (Q : Matrix (Fin m) (Fin m) E) (a : Fin n → Fˣ) :
    Matrix (Fin (m * n)) (Fin (m * n)) E :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv (Q ⊗ₖ multiplicityForm a)

def weightedTensorUnitary (σ : E ≃ₐ[F] E) (Q : Matrix (Fin m) (Fin m) E) (a : Fin n → Fˣ) :
    DualPair.Construction.unitaryGroup σ Q →* DualPair.Construction.unitaryGroup σ (weightedTensorForm Q a) :=
  (unitaryReindex σ finProdFinEquiv (Q ⊗ₖ multiplicityForm a)).comp (leftTensorUnitary σ Q (multiplicityForm a))

theorem weightedTensorForm_nondegenerate (Q : Matrix (Fin m) (Fin m) E) (hQ : Q.det ≠ 0)
    (a : Fin n → Fˣ) : (weightedTensorForm Q a).det ≠ 0 := by
  rw [weightedTensorForm, Matrix.det_reindex_self, Matrix.det_kronecker]
  exact mul_ne_zero (pow_ne_zero _ hQ) (pow_ne_zero _ (multiplicityForm_nondegenerate a))

theorem weightedTensorForm_skew (σ : E ≃ₐ[F] E) (Q : Matrix (Fin m) (Fin m) E)
    (hQ : DualPair.Construction.adjointMatrix σ Q = -Q) (a : Fin n → Fˣ) :
    DualPair.Construction.adjointMatrix σ (weightedTensorForm Q a) = -weightedTensorForm Q a := by
  rw [weightedTensorForm, adjointMatrix_reindex, DualPair.Construction.adjointMatrix_kronecker, hQ, multiplicityForm_hermitian,
    matrixKronecker_neg_left]
  rfl

theorem weightedTensorUnitary_generic (σ : E ≃ₐ[F] E) (Q : Matrix (Fin m) (Fin m) E)
    (a : Fin n → Fˣ) (g : DualPair.Construction.unitaryGroup σ Q) (hg : g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q) :
    weightedTensorUnitary σ Q a g ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ (weightedTensorForm Q a) :=
  (unitaryReindex_generic σ finProdFinEquiv _ _).mpr (leftTensorUnitary_generic σ Q _ g hg)

theorem weightedTensor_product_discriminant (σ : E ≃ₐ[F] E) (Q : Matrix (Fin m) (Fin m) E)
    (a : Fin n → Fˣ) (g h : DualPair.Construction.unitaryGroup σ Q) (hgh : g * h ∈ UnitarySplitting.Generic.Construction.unitaryGenericDomain σ Q)
    (b : Fˣ) (hb : algebraMap F E (b : F) = (CayleyProduct.Construction.unitaryProductForm σ Q g h).det) :
    algebraMap F E ((b ^ n * (∏ i, a i) ^ m : Fˣ) : F) =
      (CayleyProduct.Construction.unitaryProductForm σ (weightedTensorForm Q a) (weightedTensorUnitary σ Q a g)
        (weightedTensorUnitary σ Q a h)).det := by
  change _ = (CayleyProduct.Construction.unitaryProductForm σ (Matrix.reindex finProdFinEquiv finProdFinEquiv (Q ⊗ₖ multiplicityForm a))
    (unitaryReindex σ finProdFinEquiv _ (leftTensorUnitary σ Q (multiplicityForm a) g))
    (unitaryReindex σ finProdFinEquiv _ (leftTensorUnitary σ Q (multiplicityForm a) h))).det
  rw [unitaryProductForm_reindex, Matrix.det_reindex_self,
    leftTensorUnitary_productForm_det σ Q (multiplicityForm a) g h hgh,
    multiplicityForm_det, Fintype.card_fin, Fintype.card_fin,
    Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_mul, map_pow, map_pow, hb]

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.TensorUnitary.Construction
