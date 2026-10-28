import OAI.LinearAlgebra.Moore.Elliptic
import OAI.Analysis.PDE.Dirichlet.Quaternion

/-! The faithful complex representation preserves the actual quaternionic quadratic form. -/

noncomputable section

namespace OAI.LinearAlgebra.Moore

open scoped MatrixOrder ComplexOrder
open Matrix OAI.Analysis.PDE.Dirichlet OAI.Analysis.Calculus.Quaternion

/-- The first column of the complex representation identifies a quaternion vector with
the full complex vector space of twice the dimension. -/
def complexVector {n : ℕ} (z : Fin n → Quaternion ℝ) : Fin n × Fin 2 → ℂ :=
  fun i ↦ quaternionMatrix (z i.1) i.2 0

def quaternionVector {n : ℕ} (v : Fin n × Fin 2 → ℂ) : Fin n → Quaternion ℝ :=
  fun i ↦ ⟨(v (i, 0)).re, (v (i, 0)).im, -(v (i, 1)).re, (v (i, 1)).im⟩

@[simp] theorem complexVector_quaternionVector {n : ℕ} (v : Fin n × Fin 2 → ℂ) :
    complexVector (quaternionVector v) = v := by
  funext ⟨i, a⟩
  fin_cases a <;> apply Complex.ext <;> simp [complexVector, quaternionVector, quaternionMatrix]

@[simp] theorem quaternionVector_complexVector {n : ℕ} (z : Fin n → Quaternion ℝ) :
    quaternionVector (complexVector z) = z := by
  funext i
  ext <;> simp [complexVector, quaternionVector, quaternionMatrix]

@[simp] theorem complexVector_zero (n : ℕ) : complexVector (0 : Fin n → Quaternion ℝ) = 0 := by
  funext ⟨i, a⟩
  fin_cases a <;> apply Complex.ext <;> simp [complexVector, quaternionMatrix]

@[simp] theorem quaternionVector_zero (n : ℕ) :
    quaternionVector (0 : Fin n × Fin 2 → ℂ) = 0 := by
  funext i
  ext <;> simp [quaternionVector]

theorem complexVector_injective (n : ℕ) :
    Function.Injective (complexVector (n := n)) :=
  Function.LeftInverse.injective quaternionVector_complexVector

theorem quaternionVector_injective (n : ℕ) :
    Function.Injective (quaternionVector (n := n)) :=
  Function.LeftInverse.injective complexVector_quaternionVector

theorem quaternionMatrix_triple_entry (p q r : Quaternion ℝ) :
    quaternionMatrix (star p * q * r) 0 0 =
      ∑ a : Fin 2, ∑ b : Fin 2,
        star (quaternionMatrix p a 0) * quaternionMatrix q a b * quaternionMatrix r b 0 := by
  rw [quaternionMatrix_mul, quaternionMatrix_mul, quaternionMatrix_star]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Exact complex-valued quadratic-form identity, before taking real parts. -/
theorem complexVector_quadratic {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (z : Fin n → Quaternion ℝ) :
    star (complexVector z) ⬝ᵥ complexify A *ᵥ complexVector z =
      quaternionMatrix (OAI.Analysis.PDE.Dirichlet.quaternionForm A z) 0 0 := by
  change _ = quaternionMatrixHom (∑ i, ∑ j, star (z i) * A i j * z j) 0 0
  simp only [map_sum, Matrix.sum_apply]
  change _ = ∑ i, ∑ j, quaternionMatrix (star (z i) * A i j * z j) 0 0
  simp only [quaternionMatrix_triple_entry]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum,
    complexVector, complexify, Pi.star_apply, mul_assoc]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem complexVector_quadratic_re {n : ℕ} (A : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (z : Fin n → Quaternion ℝ) :
    (star (complexVector z) ⬝ᵥ complexify A *ᵥ complexVector z).re =
      (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re := by
  rw [complexVector_quadratic]
  rfl

theorem hermitian_quadratic_im {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (v : ι → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).im = 0 := by
  have h := congrArg Complex.im (hA.star_dotProduct_mulVec_comm v v)
  simp only [Complex.star_def, Complex.conj_im] at h
  linarith

/-- Positivity in the complex representation is precisely positivity of the original
quaternionic form, not an additional analytic assumption. -/
theorem complexify_posSemidef_iff {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hA : A.IsHermitian) :
    (complexify A).PosSemidef ↔ ∀ z, 0 ≤ (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re := by
  constructor
  · intro h z
    have hz := h.dotProduct_mulVec_nonneg (complexVector z)
    have hre := (Complex.nonneg_iff.mp hz).1
    simpa only [complexVector_quadratic_re] using hre
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (complexify_isHermitian hA) ?_
    intro v
    apply Complex.nonneg_iff.mpr
    constructor
    · have hz := h (quaternionVector v)
      rwa [← complexVector_quadratic_re, complexVector_quaternionVector] at hz
    · exact (hermitian_quadratic_im (complexify_isHermitian hA) v).symm

theorem complexify_posDef_iff {n : ℕ}
    {A : Matrix (Fin n) (Fin n) (Quaternion ℝ)} (hA : A.IsHermitian) :
    (complexify A).PosDef ↔ ∀ z ≠ 0, 0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re := by
  constructor
  · intro h z hz
    have hcz : complexVector z ≠ 0 := by
      intro heq
      exact hz ((complexVector_injective n) (heq.trans (complexVector_zero n).symm))
    have hq := h.dotProduct_mulVec_pos hcz
    have hre := (Complex.pos_iff.mp hq).1
    simpa only [complexVector_quadratic_re] using hre
  · intro h
    refine Matrix.PosDef.of_dotProduct_mulVec_pos (complexify_isHermitian hA) ?_
    intro v hv
    have hqv : quaternionVector v ≠ 0 := by
      intro heq
      exact hv ((quaternionVector_injective n) (heq.trans (quaternionVector_zero n).symm))
    apply Complex.pos_iff.mpr
    constructor
    · have hz := h (quaternionVector v) hqv
      rwa [← complexVector_quadratic_re, complexVector_quaternionVector] at hz
    · exact (hermitian_quadratic_im (complexify_isHermitian hA) v).symm

/-- A nonnegative real coordinate Hessian produces a nonnegative quaternionic
Hessian also in the faithful representation used to linearize the determinant. -/
theorem complexify_hessianMap_posSemidef {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ} (hH : H.PosSemidef) :
    (complexify (OAI.Analysis.Calculus.Quaternion.hessianMap e H)).PosSemidef := by
  apply (complexify_posSemidef_iff (OAI.Analysis.Calculus.Quaternion.hessianMap_isHermitian e H hH.isHermitian.isSymm)).mpr
  exact OAI.Analysis.PDE.Dirichlet.hessianMap_nonneg e hH

/-- The determinant differential is nonnegative in an actual nonnegative real
Hessian direction. The background positivity is expressed in quaternionic coordinates. -/
theorem mooreDifferential_hessianMap_nonneg {n s : ℕ}
    (e : Fin s → Quaternion ℝ) (A C : Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (hA : A.IsHermitian) (hpos : ∀ z ≠ 0, 0 < (OAI.Analysis.PDE.Dirichlet.quaternionForm A z).re)
    (hAC : A * C = 1) (hCA : C * A = 1) (hdet : 0 ≤ mooreDet n A)
    {H : Matrix (Fin n × Fin s) (Fin n × Fin s) ℝ} (hH : H.PosSemidef) :
    0 ≤ mooreDifferential n A (OAI.Analysis.Calculus.Quaternion.hessianMap e H) := by
  exact mooreDifferential_nonneg n A (OAI.Analysis.Calculus.Quaternion.hessianMap e H) C
    ((complexify_posDef_iff hA).mpr hpos) (complexify_hessianMap_posSemidef e hH)
    hAC hCA hdet

end OAI.LinearAlgebra.Moore
