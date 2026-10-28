import OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

/-! # Quadratic Commutator -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization

noncomputable section

section

/-! Quadratic Heisenberg covariance over a rational algebra, including finite adeles. -/

open scoped _root_.Matrix
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι K : Type*} [Fintype ι] [CommRing K] [Algebra ℚ K]

def ringQuadratic (B : Matrix ι ι K) (x : ι → K) : K :=
  algebraMap ℚ K (1 / 2) * (x ⬝ᵥ (B *ᵥ x))

theorem ringQuadratic_entries (B : Matrix ι ι K) (x : ι → K) :
    ringQuadratic B x = ∑ i, ∑ j, x i * (algebraMap ℚ K (1 / 2) * B i j) * x j := by
  simp only [ringQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem ringQuadratic_neg (B : Matrix ι ι K) (x : ι → K) :
    ringQuadratic (-B) x = -ringQuadratic B x := by
  simp only [ringQuadratic, Matrix.neg_mulVec, dotProduct_neg, mul_neg]

theorem ringQuadratic_smul_matrix (a : K) (B : Matrix ι ι K) (x : ι → K) :
    ringQuadratic (a • B) x = a * ringQuadratic B x := by
  simp only [ringQuadratic, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  ring

theorem ringQuadratic_smul_vector (a : K) (B : Matrix ι ι K) (x : ι → K) :
    ringQuadratic B (a • x) = a ^ 2 * ringQuadratic B x := by
  simp only [ringQuadratic, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
    smul_eq_mul]
  ring

theorem ringQuadratic_sub (B : Matrix ι ι K) (hB : B.IsSymm) (x q : ι → K) :
    ringQuadratic B x - ringQuadratic B (x - q) =
      (B *ᵥ q) ⬝ᵥ (x - algebraMap ℚ K (1 / 2) • q) := by
  have hcross : q ⬝ᵥ (B *ᵥ x) = x ⬝ᵥ (B *ᵥ q) := by
    simpa only [hB.eq] using Matrix.dotProduct_transpose_mulVec B q x
  have hh : (2 : K) * algebraMap ℚ K (1 / 2) = 1 := by
    have h := congrArg (algebraMap ℚ K) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
    simpa only [map_mul, map_ofNat, map_one] using h
  rw [ringQuadratic, ringQuadratic, dotProduct_comm (B *ᵥ q)]
  simp only [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct,
    smul_dotProduct, smul_eq_mul]
  rw [hcross]
  linear_combination (x ⬝ᵥ (B *ᵥ q)) * hh

theorem ringQuadratic_heisenberg (ψ : AddChar K ℂ) (B : Matrix ι ι K)
    (hB : B.IsSymm) (p q x : ι → K) (f : (ι → K) → ℂ) :
    ψ (ringQuadratic B x) * Theta.PoissonAutomorphyNormalizationData.heisenberg ψ p q f x =
      Theta.PoissonAutomorphyNormalizationData.heisenberg ψ (p + B *ᵥ q) q (fun y => ψ (ringQuadratic B y) * f y) x := by
  unfold Theta.PoissonAutomorphyNormalizationData.heisenberg
  rw [← mul_assoc, ← ψ.map_add_eq_mul, ← mul_assoc, ← ψ.map_add_eq_mul]
  congr 2
  have h := ringQuadratic_sub B hB x q
  change ringQuadratic B x + p ⬝ᵥ (x - algebraMap ℚ K (1 / 2) • q) =
    (p + B *ᵥ q) ⬝ᵥ (x - algebraMap ℚ K (1 / 2) • q) + ringQuadratic B (x - q)
  rw [add_dotProduct]
  linear_combination h

variable [DecidableEq ι]

def ringUpper (B : Matrix ι ι K) (hB : B.IsSymm) : Theta.PoissonAutomorphyNormalizationData.Sp ι K := by
  refine ⟨Matrix.fromBlocks 1 B 0 1, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [hB.eq]

omit [Algebra ℚ K] in
theorem ringUpper_phase (B : Matrix ι ι K) (hB : B.IsSymm) (p q : ι → K) :
    (ringUpper B hB).val *ᵥ Sum.elim p q = Sum.elim (p + B *ᵥ q) q := by
  funext i
  cases i <;>
    simp [ringUpper, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      Matrix.fromBlocks, Matrix.one_apply]

end

/-! A rational dilation expresses every finite-adelic upper unipotent as a commutator. -/

open scoped Classical _root_.Matrix commutatorElement
open _root_.Matrix OAI.RepresentationTheory.Theta.PoissonAutomorphyNormalizationData

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def ringLevi {K : Type*} [CommRing K] (A : (Matrix ι ι K)ˣ) : Theta.PoissonAutomorphyNormalizationData.Sp ι K := by
  refine ⟨Matrix.fromBlocks A.val 0 0 (A⁻¹).val.transpose, ?_⟩
  rw [SymplecticGroup.fromBlocks_mem_iff]
  simp [← Matrix.transpose_mul]

def rationalDoubleMatrix : (Matrix ι ι ℚ)ˣ where
  val := (2 : ℚ) • 1
  inv := (1 / 2 : ℚ) • 1
  val_inv := by simp [smul_smul]
  inv_val := by simp [smul_smul]

def rationalDoubleSymplectic : Theta.PoissonAutomorphyNormalizationData.Sp ι ℚ := ringLevi rationalDoubleMatrix

theorem rationalDoubleSymplectic_map {K : Type*} [CommRing K] [Algebra ℚ K] :
    (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ K) (rationalDoubleSymplectic (ι := ι))).val =
      Matrix.fromBlocks ((2 : K) • 1) 0 0 (algebraMap ℚ K (1 / 2) • 1) := by
  have hmap (a : ℚ) : ((a • (1 : Matrix ι ι ℚ)).map (algebraMap ℚ K)) =
      algebraMap ℚ K a • (1 : Matrix ι ι K) := by
    apply Matrix.ext
    intro i j
    change (algebraMap ℚ K) (a * (if i = j then 1 else 0)) =
      (algebraMap ℚ K) a * (if i = j then 1 else 0)
    by_cases hij : i = j <;> simp [hij]
  change (Matrix.fromBlocks ((2 : ℚ) • (1 : Matrix ι ι ℚ)) 0 0
    ((1 / 2 : ℚ) • (1 : Matrix ι ι ℚ)).transpose).map (algebraMap ℚ K) = _
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.fromBlocks_map]
  rw [hmap 2, hmap (1 / 2)]
  simp only [map_ofNat, Matrix.map_zero _ (map_zero (algebraMap ℚ K))]

theorem scalar_upper_matrix_relation {K : Type*} [CommRing K]
    (a b c : K) (h : a * c = (1 + c) * b) (B : Matrix ι ι K) :
    Matrix.fromBlocks (a • (1 : Matrix ι ι K)) 0 0 (b • (1 : Matrix ι ι K)) *
        Matrix.fromBlocks (1 : Matrix ι ι K) (c • B) 0 (1 : Matrix ι ι K) =
      Matrix.fromBlocks (1 : Matrix ι ι K) B 0 (1 : Matrix ι ι K) *
        Matrix.fromBlocks (1 : Matrix ι ι K) (c • B) 0 (1 : Matrix ι ι K) *
        Matrix.fromBlocks (a • (1 : Matrix ι ι K)) 0 0 (b • (1 : Matrix ι ι K)) := by
  simp only [Matrix.fromBlocks_multiply, zero_mul, mul_zero, one_mul, mul_one,
    zero_add, add_zero, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  apply Matrix.ext
  intro i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  linear_combination (B i j) * h

theorem rationalDouble_upper_commutator {K : Type*} [CommRing K] [Algebra ℚ K]
    (B : Matrix ι ι K) (hB : B.IsSymm) :
    ⁅Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ K) (rationalDoubleSymplectic (ι := ι)),
      ringUpper (algebraMap ℚ K (1 / 3) • B) (hB.smul _)⁆ = ringUpper B hB := by
  have hc : (2 : K) * algebraMap ℚ K (1 / 3) =
      (1 + algebraMap ℚ K (1 / 3)) * algebraMap ℚ K (1 / 2) := by
    have h := congrArg (algebraMap ℚ K)
      (show (2 : ℚ) * (1 / 3) = (1 + 1 / 3) * (1 / 2) by norm_num)
    simpa only [map_mul, map_add, map_one, map_ofNat] using h
  have hrel : Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ K) (rationalDoubleSymplectic (ι := ι)) *
      ringUpper (algebraMap ℚ K (1 / 3) • B) (hB.smul _) =
      ringUpper B hB * ringUpper (algebraMap ℚ K (1 / 3) • B) (hB.smul _) *
        Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ K) (rationalDoubleSymplectic (ι := ι)) := by
    apply Subtype.ext
    change (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ K) rationalDoubleSymplectic).val *
      Matrix.fromBlocks 1 (algebraMap ℚ K (1 / 3) • B) 0 1 =
      Matrix.fromBlocks 1 B 0 1 * Matrix.fromBlocks 1 (algebraMap ℚ K (1 / 3) • B) 0 1 *
        (Theta.PoissonAutomorphyNormalizationData.mapSp (algebraMap ℚ K) rationalDoubleSymplectic).val
    rw [rationalDoubleSymplectic_map]
    exact scalar_upper_matrix_relation _ _ _ hc B
  rw [commutatorElement_def, hrel]
  simp only [mul_assoc, mul_inv_cancel, mul_one]

end

end OAI.RepresentationTheory.Hecke.RadialDilation.QuadraticCommutator.Realization
