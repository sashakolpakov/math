import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.Relations

/-! # Chart Relations -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartRelations.Grassmannian

noncomputable section

/-! Explicit homogeneous relations that recover the normalized projective charts. -/

open _root_.MvPolynomial

universe u v w z

variable {R : Type u} [CommRing R] {B : Type z} [CommRing B]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

theorem maximalMinor_update_selected (a : ι → ν) (Q : Matrix ι ν R) (i j : ι) :
    Determinants.Grassmannian.maximalMinor Q (Function.update a i (a j)) = if i = j then Determinants.Grassmannian.maximalMinor Q a else 0 := by
  rw [Determinants.Grassmannian.maximalMinor, Determinants.Grassmannian.selectedColumns_update]
  by_cases h : i = j
  · subst j
    change ((Normalized.Matrices.Grassmannian.selectedColumns a Q).updateCol i (fun j => Normalized.Matrices.Grassmannian.selectedColumns a Q j i)).det =
      if i = i then Determinants.Grassmannian.maximalMinor Q a else 0
    rw [Matrix.updateCol_eq_self, ite_eq_left rfl]
    rfl
  · rw [ite_eq_right h]
    exact Matrix.det_updateCol_eq_zero (Ne.symm h)

theorem scaled_replacement_determinant (a b : ι → ν) (Q : Matrix ι ν R) (r : R) :
    (Determinants.Grassmannian.maximalMinor Q a * r) *
        Matrix.det (fun i j : ι => Determinants.Grassmannian.maximalMinor Q (Function.update a i (b j)) * r) =
      (Determinants.Grassmannian.maximalMinor Q a * r) ^ Fintype.card ι * (Determinants.Grassmannian.maximalMinor Q b * r) := by
  have hM : (fun i j => Determinants.Grassmannian.maximalMinor Q (Function.update a i (b j)) * r : Matrix ι ι R) =
      r • Normalized.Matrices.Grassmannian.selectedColumns b (Determinants.Grassmannian.replacementMinors a Q) := by
    ext i j
    exact mul_comm _ _
  rw [hM, Matrix.det_smul]
  change (Determinants.Grassmannian.maximalMinor Q a * r) *
    (r ^ Fintype.card ι * Determinants.Grassmannian.maximalMinor (Determinants.Grassmannian.replacementMinors a Q) b) = _
  calc
    _ = (Determinants.Grassmannian.maximalMinor Q a * Determinants.Grassmannian.maximalMinor (Determinants.Grassmannian.replacementMinors a Q) b) *
        (r ^ Fintype.card ι * r) := by ring
    _ = (Determinants.Grassmannian.maximalMinor Q a ^ Fintype.card ι * Determinants.Grassmannian.maximalMinor Q b) *
        (r ^ Fintype.card ι * r) := by rw [Relations.Grassmannian.replacementMinors_determinant_homogeneous]
    _ = _ := by rw [mul_pow]; ring

def pluckerChartRelation (a b : ι → ν) : MvPolynomial (ι → ν) R :=
  X a * Matrix.det (fun i j : ι => (X (Function.update a i (b j)) : MvPolynomial (ι → ν) R)) -
    X a ^ Fintype.card ι * X b

theorem eval₂_pluckerChartRelation (φ : R →+* B) (Q : Matrix ι ν B) (r : B) (a b : ι → ν) :
    eval₂Hom φ (fun c => Determinants.Grassmannian.maximalMinor Q c * r) (pluckerChartRelation (R := R) a b) = 0 := by
  let E := eval₂Hom φ (fun c => Determinants.Grassmannian.maximalMinor Q c * r)
  let M : Matrix ι ι (MvPolynomial (ι → ν) R) := fun i j => X (Function.update a i (b j))
  have hM : E.mapMatrix M =
      (fun i j => Determinants.Grassmannian.maximalMinor Q (Function.update a i (b j)) * r : Matrix ι ι B) := by
    ext i j
    exact eval₂Hom_X' φ (fun c => Determinants.Grassmannian.maximalMinor Q c * r) _
  change E (pluckerChartRelation a b) = 0
  rw [pluckerChartRelation, map_sub, sub_eq_zero, map_mul, map_mul, map_pow]
  have hdet := (E.map_det M).trans (congrArg Matrix.det hM)
  change E (X a) * E M.det = E (X a) ^ Fintype.card ι * E (X b)
  rw [hdet]
  simpa only [E, eval₂Hom_X'] using scaled_replacement_determinant a b Q r

def pluckerPivotRelation (a : ι → ν) (i j : ι) : MvPolynomial (ι → ν) R :=
  X (Function.update a i (a j)) - if i = j then X a else 0

theorem eval₂_pluckerPivotRelation (φ : R →+* B) (Q : Matrix ι ν B) (r : B)
    (a : ι → ν) (i j : ι) :
    eval₂Hom φ (fun c => Determinants.Grassmannian.maximalMinor Q c * r) (pluckerPivotRelation (R := R) a i j) = 0 := by
  unfold pluckerPivotRelation
  rw [map_sub, sub_eq_zero, eval₂Hom_X', maximalMinor_update_selected]
  by_cases h : i = j
  · simp only [ite_eq_left h, eval₂Hom_X']
  · simp only [ite_eq_right h, zero_mul, map_zero]

theorem pluckerEvaluation_as_minors :
    Ideal.Grassmannian.pluckerEvaluation (R := R) (ι := ι) (ν := ν) =
      eval₂Hom (C.comp C) (fun a =>
        Determinants.Grassmannian.maximalMinor ((Ideal.Grassmannian.genericQuotientMatrix (R := R) (ι := ι) (ν := ν)).map C) a * X ()) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [Ideal.Grassmannian.pluckerEvaluation]
  · intro a
    rw [Ideal.Grassmannian.pluckerEvaluation_X, eval₂Hom_X', Determinants.Grassmannian.maximalMinor_map]
    rfl

theorem pluckerChartRelation_mem (a b : ι → ν) :
    pluckerChartRelation (R := R) a b ∈ Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν) := by
  apply (Ideal.Grassmannian.mem_pluckerIdeal _).mpr
  rw [pluckerEvaluation_as_minors]
  exact eval₂_pluckerChartRelation _ _ _ a b

theorem pluckerPivotRelation_mem (a : ι → ν) (i j : ι) :
    pluckerPivotRelation (R := R) a i j ∈ Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν) := by
  apply (Ideal.Grassmannian.mem_pluckerIdeal _).mpr
  rw [pluckerEvaluation_as_minors]
  exact eval₂_pluckerPivotRelation _ _ _ a i j

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartRelations.Grassmannian
