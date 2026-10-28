import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Normalized.Matrices

/-! # Determinants -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Determinants.Grassmannian

noncomputable section

/-!
Determinant identities for the Plücker coordinates of quotient matrices.
Replacing one selected column recovers affine chart coordinates, and the
full determinant identity holds over every commutative coefficient ring.
-/

universe u v w

variable {R : Type u} [CommRing R]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

def maximalMinor (Q : Matrix ι ν R) (a : ι → ν) : R := (Normalized.Matrices.Grassmannian.selectedColumns a Q).det

def replacementMinors (a : ι → ν) (Q : Matrix ι ν R) : Matrix ι ν R :=
  fun i v => maximalMinor Q (Function.update a i v)

omit [CommRing R] [Fintype ι] in
theorem selectedColumns_update (a : ι → ν) (Q : Matrix ι ν R) (i : ι) (v : ν) :
    Normalized.Matrices.Grassmannian.selectedColumns (Function.update a i v) Q =
      (Normalized.Matrices.Grassmannian.selectedColumns a Q).updateCol i (fun j => Q j v) := by
  ext j k
  by_cases h : k = i
  · subst k
    simp [Normalized.Matrices.Grassmannian.selectedColumns, Matrix.updateCol]
  · simp [Normalized.Matrices.Grassmannian.selectedColumns, Matrix.updateCol, h]

theorem replacementMinors_eq_adjugate (a : ι → ν) (Q : Matrix ι ν R) :
    replacementMinors a Q = (Normalized.Matrices.Grassmannian.selectedColumns a Q).adjugate * Q := by
  ext i v
  change (Normalized.Matrices.Grassmannian.selectedColumns (Function.update a i v) Q).det = _
  rw [selectedColumns_update, ← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

theorem replacementMinors_of_normalized (a : ι → ν) (Q : Matrix ι ν R)
    (h : Normalized.Matrices.Grassmannian.IsNormalized a Q) : replacementMinors a Q = Q := by
  rw [replacementMinors_eq_adjugate, h, Matrix.adjugate_one, Matrix.one_mul]

/-- The determinant relation expressing all minors in the affine coordinates
of a selected chart; this includes the zero-rank case. -/
theorem replacementMinors_determinant (a b : ι → ν) (Q : Matrix ι ν R) :
    maximalMinor (replacementMinors a Q) b =
      maximalMinor Q a ^ (Fintype.card ι - 1) * maximalMinor Q b := by
  unfold maximalMinor
  rw [replacementMinors_eq_adjugate, Normalized.Matrices.Grassmannian.selectedColumns_mul, Matrix.det_mul, Matrix.det_adjugate]

theorem maximalMinor_normalized (a : ι → ν) (Q : Matrix ι ν R) (h : Normalized.Matrices.Grassmannian.IsNormalized a Q) :
    maximalMinor Q a = 1 := by
  rw [maximalMinor, h, Matrix.det_one]

theorem maximalMinor_map {S : Type*} [CommRing S] (φ : R →+* S)
    (a : ι → ν) (Q : Matrix ι ν R) : maximalMinor (Q.map φ) a = φ (maximalMinor Q a) :=
  (φ.map_det (Normalized.Matrices.Grassmannian.selectedColumns a Q)).symm

theorem maximalMinor_normalize (a b : ι → ν) (Q : Matrix ι ν R)
    (h : IsUnit (maximalMinor Q a)) :
    maximalMinor Q a * maximalMinor (Normalized.Matrices.Grassmannian.normalizeColumns a Q) b = maximalMinor Q b := by
  change (Normalized.Matrices.Grassmannian.selectedColumns a Q).det * (Normalized.Matrices.Grassmannian.selectedColumns b (Normalized.Matrices.Grassmannian.normalizeColumns a Q)).det = _
  rw [Normalized.Matrices.Grassmannian.selectedColumns_normalize, Matrix.det_mul, ← mul_assoc]
  have hi : (Normalized.Matrices.Grassmannian.selectedColumns a Q).det * (Normalized.Matrices.Grassmannian.selectedColumns a Q)⁻¹.det = 1 := by
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv _ h, Matrix.det_one]
  rw [hi, one_mul]
  rfl

theorem maximalMinors_injective_on_normalized (a : ι → ν) (Q K : Matrix ι ν R)
    (hQ : Normalized.Matrices.Grassmannian.IsNormalized a Q) (hK : Normalized.Matrices.Grassmannian.IsNormalized a K)
    (h : ∀ b, maximalMinor Q b = maximalMinor K b) : Q = K := by
  rw [← replacementMinors_of_normalized a Q hQ, ← replacementMinors_of_normalized a K hK]
  ext i v
  exact h (Function.update a i v)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Determinants.Grassmannian
