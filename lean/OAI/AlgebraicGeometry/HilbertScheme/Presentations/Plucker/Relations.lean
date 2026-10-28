import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Ideal

/-! # Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Relations.Grassmannian

noncomputable section

/-!
Universal specialization of the homogeneous determinant-relation ideal and
the homogeneous replacement-minor identity used on projective charts.
-/

open _root_.MvPolynomial

universe u v w z

variable {R : Type u} [CommRing R] {B : Type z} [CommRing B]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

theorem replacementMinors_determinant_homogeneous (a b : ι → ν) (Q : Matrix ι ν R) :
    Determinants.Grassmannian.maximalMinor Q a * Determinants.Grassmannian.maximalMinor (Determinants.Grassmannian.replacementMinors a Q) b =
      Determinants.Grassmannian.maximalMinor Q a ^ Fintype.card ι * Determinants.Grassmannian.maximalMinor Q b := by
  unfold Determinants.Grassmannian.maximalMinor
  rw [Determinants.Grassmannian.replacementMinors_eq_adjugate, Normalized.Matrices.Grassmannian.selectedColumns_mul, ← Matrix.det_mul,
    ← Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, Matrix.det_smul]

theorem eval₂_pluckerMinorPolynomial (φ : R →+* B) (Q : Matrix ι ν B) (a : ι → ν) :
    eval₂ φ (fun p : ι × ν => Q p.1 p.2) (Ideal.Grassmannian.pluckerMinorPolynomial (R := R) a) =
      Determinants.Grassmannian.maximalMinor Q a := by
  change (eval₂Hom φ (fun p : ι × ν => Q p.1 p.2))
    (Determinants.Grassmannian.maximalMinor (Ideal.Grassmannian.genericQuotientMatrix (R := R)) a) = _
  rw [← Determinants.Grassmannian.maximalMinor_map]
  congr 1
  ext i j
  exact eval₂_X φ (fun p : ι × ν => Q p.1 p.2) (i, j)

def scaledMatrixSpecialization (φ : R →+* B) (Q : Matrix ι ν B) (r : B) :
    MvPolynomial Unit (MvPolynomial (ι × ν) R) →+* B :=
  eval₂Hom (eval₂Hom φ (fun p : ι × ν => Q p.1 p.2)) (fun _ => r)

theorem scaledMatrixSpecialization_pluckerEvaluation (φ : R →+* B) (Q : Matrix ι ν B) (r : B) :
    (scaledMatrixSpecialization φ Q r).comp (Ideal.Grassmannian.pluckerEvaluation (R := R) (ι := ι) (ν := ν)) =
      eval₂Hom φ (fun a => Determinants.Grassmannian.maximalMinor Q a * r) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [scaledMatrixSpecialization, Ideal.Grassmannian.pluckerEvaluation]
  · intro a
    simp only [RingHom.comp_apply, Ideal.Grassmannian.pluckerEvaluation_X, map_mul,
      scaledMatrixSpecialization, eval₂Hom_C, eval₂Hom_X']
    exact congrArg (fun x => x * r) (eval₂_pluckerMinorPolynomial φ Q a)

/-- Every homogeneous Plücker relation vanishes on every scaled tuple of
actual matrix minors, after any change of coefficient ring. -/
theorem pluckerIdeal_vanish (φ : R →+* B) (Q : Matrix ι ν B) (r : B)
    (p : MvPolynomial (ι → ν) R)
    (hp : p ∈ Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν)) :
    eval₂ φ (fun a => Determinants.Grassmannian.maximalMinor Q a * r) p = 0 := by
  have h := congrArg (scaledMatrixSpecialization φ Q r) ((Ideal.Grassmannian.mem_pluckerIdeal p).mp hp)
  rw [map_zero] at h
  change ((scaledMatrixSpecialization φ Q r).comp
    (Ideal.Grassmannian.pluckerEvaluation (R := R) (ι := ι) (ν := ν))) p = 0 at h
  rw [scaledMatrixSpecialization_pluckerEvaluation] at h
  exact h

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Relations.Grassmannian
