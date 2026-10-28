import Mathlib

/-! Algebraic quaternionic Hessian and current identities from
`sections/calculus.tex` and `sections/current.tex`.

`hessianMap` acts on an ordinary real Hessian, exactly as in equation
(quaternionic-hessian), and permits either three or four real slots.
-/

namespace OAI.Analysis.Calculus.Quaternion

open scoped Matrix

noncomputable section

abbrev Q := Quaternion ℝ

/-- Quaternionic gradient of a real covector in the chosen slots. -/
def gradientMap {m s : Type*} [Fintype s] (e : s → Q)
    (ξ : m × s → ℝ) (a : m) : Q := ∑ α, ξ (a, α) • e α

/-- The real-linear Hessian map used in the manuscript. -/
def hessianMap {m s : Type*} [Fintype s] (e : s → Q)
    (H : Matrix (m × s) (m × s) ℝ) : Matrix m m Q :=
  fun a b => ∑ α, ∑ β, H (a, α) (b, β) • (e α * star (e β))

/-- A quaternionic outer product, with the order of multiplication fixed. -/
def outer {m : Type*} (g : m → Q) : Matrix m m Q :=
  fun a b => g a * star (g b)

private theorem re_sum {ι : Type*} (t : Finset ι) (f : ι → Q) :
    (∑ i ∈ t, f i).re = ∑ i ∈ t, (f i).re := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

private theorem coe_sum {ι : Type*} (t : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ t, f i : ℝ) : Q) = ∑ i ∈ t, (f i : Q) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, Quaternion.coe_add]

/-- The four standard quaternionic slots. -/
def fourSlots : Fin 4 → Q := ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The three real slots used by the current construction. -/
def threeSlots : Fin 3 → Q := ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩]

theorem fourSlots_orthonormal (α β : Fin 4) :
    (fourSlots α * star (fourSlots β)).re = if α = β then 1 else 0 := by
  fin_cases α <;> fin_cases β <;> norm_num [fourSlots, Quaternion.re_mul]

theorem threeSlots_orthonormal (α β : Fin 3) :
    (threeSlots α * star (threeSlots β)).re = if α = β then 1 else 0 := by
  fin_cases α <;> fin_cases β <;> norm_num [threeSlots, Quaternion.re_mul]

theorem gradientMap_threeSlots {m : Type*} (ξ : m × Fin 3 → ℝ) (a : m) :
    gradientMap threeSlots ξ a = ⟨ξ (a, 0), ξ (a, 1), ξ (a, 2), 0⟩ := by
  ext <;> simp [gradientMap, threeSlots, Fin.sum_univ_three]

theorem gradientMap_fourSlots {m : Type*} (ξ : m × Fin 4 → ℝ) (a : m) :
    gradientMap fourSlots ξ a = ⟨ξ (a, 0), ξ (a, 1), ξ (a, 2), ξ (a, 3)⟩ := by
  ext <;> simp [gradientMap, fourSlots, Fin.sum_univ_four]

theorem gradientMap_threeSlots_injective {m : Type*} :
    Function.Injective (gradientMap (m := m) threeSlots) := by
  intro ξ η h
  funext ⟨a, α⟩
  have ha := congrFun h a
  rw [gradientMap_threeSlots, gradientMap_threeSlots] at ha
  fin_cases α
  · exact congrArg (fun q : Q => q.re) ha
  · exact congrArg (fun q : Q => q.imI) ha
  · exact congrArg (fun q : Q => q.imJ) ha

theorem gradientMap_fourSlots_injective {m : Type*} :
    Function.Injective (gradientMap (m := m) fourSlots) := by
  intro ξ η h
  funext ⟨a, α⟩
  have ha := congrFun h a
  rw [gradientMap_fourSlots, gradientMap_fourSlots] at ha
  fin_cases α
  · exact congrArg (fun q : Q => q.re) ha
  · exact congrArg (fun q : Q => q.imI) ha
  · exact congrArg (fun q : Q => q.imJ) ha
  · exact congrArg (fun q : Q => q.imK) ha

theorem hessianMap_diagonal_re {m s : Type*} [Fintype s] [DecidableEq s]
    (e : s → Q) (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (H : Matrix (m × s) (m × s) ℝ) (a : m) :
    (hessianMap e H a a).re = ∑ α, H (a, α) (a, α) := by
  simp only [hessianMap, re_sum, Quaternion.re_smul, smul_eq_mul, he]
  simp

theorem outer_isHermitian {m : Type*} (g : m → Q) :
    (outer g).IsHermitian := by
  apply Matrix.ext
  intro a b
  simp [Matrix.conjTranspose_apply, outer]

theorem outer_eq_zero_iff {m : Type*} (g : m → Q) : outer g = 0 ↔ g = 0 := by
  constructor
  · intro h
    funext a
    have ha : g a * star (g a) = 0 := congrFun (congrFun h a) a
    rcases mul_eq_zero.mp ha with hg | hg
    · exact hg
    · simpa using congrArg star hg
  · rintro rfl
    apply Matrix.ext
    intro a b
    simp [outer]

/-- Symmetry of the real Hessian yields Hermitian symmetry. -/
theorem hessianMap_isHermitian {m s : Type*} [Fintype s] (e : s → Q)
    (H : Matrix (m × s) (m × s) ℝ) (hH : H.IsSymm) :
    (hessianMap e H).IsHermitian := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.conjTranspose_apply, hessianMap, star_sum,
    Quaternion.star_smul, star_mul, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [hH.apply]

/-- The quaternionic trace is precisely the ordinary real trace. -/
theorem hessianMap_trace {m s : Type*} [Fintype m] [Fintype s] [DecidableEq s]
    (e : s → Q) (he : ∀ α β, (e α * star (e β)).re = if α = β then 1 else 0)
    (H : Matrix (m × s) (m × s) ℝ) (hH : H.IsSymm) :
    Matrix.trace (hessianMap e H) = ((Matrix.trace H : ℝ) : Q) := by
  have hd (a : m) : hessianMap e H a a =
      ((∑ α, H (a, α) (a, α) : ℝ) : Q) := by
    have hh := (hessianMap_isHermitian e H hH).apply a a
    rw [Quaternion.star_eq_self] at hh
    rw [hh, hessianMap_diagonal_re e he]
  simp only [Matrix.trace, Matrix.diag, hd, Fintype.sum_prod_type]
  rw [coe_sum]

/-- The Hessian map takes a real rank-one matrix to `g g*`. -/
theorem hessianMap_rankOne {m s : Type*} [Fintype s] (e : s → Q)
    (ξ : m × s → ℝ) :
    hessianMap e (fun a b => ξ a * ξ b) = outer (gradientMap e ξ) := by
  apply Matrix.ext
  intro a b
  simp only [hessianMap, outer, gradientMap, star_sum, Quaternion.star_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [mul_comm]

theorem hessianMap_rankOne_threeSlots_ne_zero {m : Type*}
    (ξ : m × Fin 3 → ℝ) (hξ : ξ ≠ 0) :
    hessianMap threeSlots (fun a b => ξ a * ξ b) ≠ 0 := by
  intro h
  rw [hessianMap_rankOne, outer_eq_zero_iff] at h
  apply hξ
  apply gradientMap_threeSlots_injective
  rw [h]
  funext a
  simp [gradientMap]

theorem hessianMap_rankOne_fourSlots_ne_zero {m : Type*}
    (ξ : m × Fin 4 → ℝ) (hξ : ξ ≠ 0) :
    hessianMap fourSlots (fun a b => ξ a * ξ b) ≠ 0 := by
  intro h
  rw [hessianMap_rankOne, outer_eq_zero_iff] at h
  apply hξ
  apply gradientMap_fourSlots_injective
  rw [h]
  funext a
  simp [gradientMap]

/-- The bilinear version of the rank-one rule. -/
theorem hessianMap_tensor {m s : Type*} [Fintype s] (e : s → Q)
    (ξ η : m × s → ℝ) :
    hessianMap e (Matrix.of (fun a b => ξ a * η b)) =
      Matrix.of (fun a b => gradientMap e ξ a * star (gradientMap e η b)) := by
  apply Matrix.ext
  intro a b
  simp only [hessianMap, Matrix.of_apply, gradientMap, star_sum, Quaternion.star_smul,
    Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm,
    Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [mul_comm]

theorem hessianMap_add {m s : Type*} [Fintype s] (e : s → Q)
    (A B : Matrix (m × s) (m × s) ℝ) :
    hessianMap e (A + B) = hessianMap e A + hessianMap e B := by
  apply Matrix.ext
  intro a b
  simp [hessianMap, add_smul, Finset.sum_add_distrib]

theorem hessianMap_smul {m s : Type*} [Fintype s] (e : s → Q)
    (A : Matrix (m × s) (m × s) ℝ) (c : ℝ) :
    hessianMap e (c • A) = c • hessianMap e A := by
  apply Matrix.ext
  intro a b
  simp [hessianMap, Finset.smul_sum, mul_smul]

/-- The algebraic product rule applied to the ordinary real Hessian product rule. -/
theorem hessian_product_algebra {m s : Type*} [Fintype s] (e : s → Q)
    (A B : Matrix (m × s) (m × s) ℝ) (u v : ℝ) (ξ η : m × s → ℝ) :
    hessianMap e (u • B + v • A + Matrix.of (fun a b => ξ a * η b) +
      Matrix.of (fun a b => η a * ξ b)) =
      u • hessianMap e B + v • hessianMap e A +
      Matrix.of (fun a b => gradientMap e ξ a * star (gradientMap e η b)) +
      Matrix.of (fun a b => gradientMap e η a * star (gradientMap e ξ b)) := by
  rw [hessianMap_add, hessianMap_add, hessianMap_add,
    hessianMap_smul, hessianMap_smul, hessianMap_tensor, hessianMap_tensor]

/-- Multiplication by an outer product has image in the right span of its column. -/
theorem outer_mulVec {m : Type*} [Fintype m] (g x : m → Q) (a : m) :
    (outer g *ᵥ x) a = g a * ∑ b, star (g b) * x b := by
  simp [Matrix.mulVec, dotProduct, outer, Finset.mul_sum, mul_assoc]

/-- The quadratic form of an outer product is a quaternionic norm square. -/
theorem outer_quadratic {m : Type*} [Fintype m] (g x : m → Q) :
    ∑ a, star (x a) * (outer g *ᵥ x) a =
      star (∑ a, star (g a) * x a) * (∑ a, star (g a) * x a) := by
  simp only [outer_mulVec, star_sum, star_mul, star_star, Finset.sum_mul, mul_assoc]

/-- In particular this quadratic form has nonnegative real part. -/
theorem outer_quadratic_nonneg {m : Type*} [Fintype m] (g x : m → Q) :
    0 ≤ (∑ a, star (x a) * (outer g *ᵥ x) a).re := by
  rw [outer_quadratic]
  simp only [Quaternion.re_mul, Quaternion.re_star, Quaternion.imI_star,
    Quaternion.imJ_star, Quaternion.imK_star]
  nlinarith [sq_nonneg (∑ a, star (g a) * x a).re,
    sq_nonneg (∑ a, star (g a) * x a).imI,
    sq_nonneg (∑ a, star (g a) * x a).imJ,
    sq_nonneg (∑ a, star (g a) * x a).imK]

/-- A left row that kills a column kills the whole image of its outer product. -/
theorem outer_image_tangent {m : Type*} [Fintype m] (ℓ g x : m → Q)
    (h : ∑ a, ℓ a * g a = 0) :
    ∑ a, ℓ a * (outer g *ᵥ x) a = 0 := by
  simp only [outer_mulVec, ← mul_assoc, ← Finset.sum_mul, h, zero_mul]

/-- Real coefficients associated to a quaternionic Hermitian form. -/
def realCoefficients {m s : Type*} (e : s → Q) (A : Matrix m m Q) :
    Matrix (m × s) (m × s) ℝ :=
  fun a b => (star (e a.2) * A a.1 b.1 * e b.2).re

theorem realCoefficients_isSymm {m s : Type*} (e : s → Q) (A : Matrix m m Q)
    (hA : A.IsHermitian) : (realCoefficients e A).IsSymm := by
  apply Matrix.ext
  intro a b
  change (star (e b.2) * A b.1 a.1 * e a.2).re =
    (star (e a.2) * A a.1 b.1 * e b.2).re
  rw [← Quaternion.re_star (star (e a.2) * A a.1 b.1 * e b.2)]
  simp only [star_mul, star_star, hA.apply b.1 a.1, mul_assoc]

/-- Strong quaternionic divergence evaluated on the first derivative array. -/
def strongDivergence {m s : Type*} [Fintype m] [Fintype s] (e : s → Q)
    (dA : m × s → Matrix m m Q) (b : m) : Q :=
  ∑ a, ∑ α, star (e α) * dA (a, α) a b

/-- Quaternionic conservation implies conservation of every real coefficient column.
The derivative array `dA` can be the derivatives of any matrix field at a point. -/
theorem realCoefficients_divergence_zero {m s : Type*} [Fintype m] [Fintype s]
    (e : s → Q) (dA : m × s → Matrix m m Q)
    (h : ∀ b, strongDivergence e dA b = 0) (b : m × s) :
    ∑ a : m × s, realCoefficients e (dA a) a b = 0 := by
  simp only [realCoefficients, Fintype.sum_prod_type]
  simp only [← re_sum, ← Finset.sum_mul]
  change (strongDivergence e dA b.1 * e b.2).re = 0
  rw [h, zero_mul]
  rfl

end
end OAI.Analysis.Calculus.Quaternion
