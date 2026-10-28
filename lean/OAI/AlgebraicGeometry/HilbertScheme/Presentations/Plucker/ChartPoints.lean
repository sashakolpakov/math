import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartRelations

/-! # Chart Points -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartPoints.Grassmannian

noncomputable section

/-!
The affine charts of the homogeneous Plücker relation ideal classify exactly
the normalized quotient matrices, over arbitrary coefficient rings.
-/

open _root_.MvPolynomial

universe u v w z

variable {R : Type u} [CommRing R] {B : Type z} [CommRing B]
variable {ι : Type v} {ν : Type w} [Fintype ι] [DecidableEq ι]

def PluckerChartPoint (φ : R →+* B) (a : ι → ν) :=
  {p : (ι → ν) → B // p a = 1 ∧ ∀ f ∈ Ideal.Grassmannian.pluckerIdeal (R := R) (ι := ι) (ν := ν), eval₂ φ p f = 0}

def pluckerChartMatrix (a : ι → ν) (p : (ι → ν) → B) : Matrix ι ν B :=
  fun i v => p (Function.update a i v)

omit [Fintype ι] in
theorem eval₂_pivotRelation (φ : R →+* B) (p : (ι → ν) → B) (a : ι → ν) (i j : ι) :
    eval₂ φ p (ChartRelations.Grassmannian.pluckerPivotRelation a i j) =
      p (Function.update a i (a j)) - if i = j then p a else 0 := by
  change eval₂Hom φ p (ChartRelations.Grassmannian.pluckerPivotRelation a i j) = _
  rw [ChartRelations.Grassmannian.pluckerPivotRelation, map_sub, eval₂Hom_X']
  by_cases h : i = j <;> simp only [h, ite_true, ite_false, eval₂Hom_X', map_zero]

theorem eval₂_chartRelation (φ : R →+* B) (p : (ι → ν) → B) (a b : ι → ν) :
    eval₂ φ p (ChartRelations.Grassmannian.pluckerChartRelation a b) = p a * Determinants.Grassmannian.maximalMinor (pluckerChartMatrix a p) b -
      p a ^ Fintype.card ι * p b := by
  let E := eval₂Hom φ p
  let M : Matrix ι ι (MvPolynomial (ι → ν) R) := fun i j => X (Function.update a i (b j))
  have hM : E.mapMatrix M =
      Normalized.Matrices.Grassmannian.selectedColumns b (pluckerChartMatrix a p) := by
    ext i j
    exact eval₂Hom_X' φ p _
  change E (ChartRelations.Grassmannian.pluckerChartRelation a b) = _
  rw [ChartRelations.Grassmannian.pluckerChartRelation, map_sub, map_mul, map_mul, map_pow]
  have hdet := (E.map_det M).trans (congrArg Matrix.det hM)
  change E (X a) * E M.det - E (X a) ^ Fintype.card ι * E (X b) = _
  rw [hdet]
  simp only [E, eval₂Hom_X']
  rfl

theorem pluckerChartMatrix_normalized (φ : R →+* B) (a : ι → ν) (p : PluckerChartPoint φ a) :
    Normalized.Matrices.Grassmannian.IsNormalized a (pluckerChartMatrix a p.val) := by
  ext i j
  have h := p.property.2 _ (ChartRelations.Grassmannian.pluckerPivotRelation_mem (R := R) a i j)
  rw [eval₂_pivotRelation, p.property.1, sub_eq_zero] at h
  exact h

theorem pluckerChartMatrix_minors (φ : R →+* B) (a : ι → ν) (p : PluckerChartPoint φ a) (b : ι → ν) :
    Determinants.Grassmannian.maximalMinor (pluckerChartMatrix a p.val) b = p.val b := by
  have h := p.property.2 _ (ChartRelations.Grassmannian.pluckerChartRelation_mem (R := R) a b)
  rw [eval₂_chartRelation, p.property.1, one_mul, one_pow, one_mul, sub_eq_zero] at h
  exact h

/-- Inverting and normalizing a Plücker coordinate produces precisely the
ordinary affine quotient-matrix chart. -/
def pluckerChartPointEquiv (φ : R →+* B) (a : ι → ν) :
    PluckerChartPoint φ a ≃ {Q : Matrix ι ν B // Normalized.Matrices.Grassmannian.IsNormalized a Q} where
  toFun p := ⟨pluckerChartMatrix a p.val, pluckerChartMatrix_normalized φ a p⟩
  invFun Q := ⟨Determinants.Grassmannian.maximalMinor Q.val, Determinants.Grassmannian.maximalMinor_normalized a Q.val Q.property, by
    intro f hf
    simpa only [mul_one] using Relations.Grassmannian.pluckerIdeal_vanish φ Q.val 1 f hf⟩
  left_inv p := Subtype.ext (funext (pluckerChartMatrix_minors φ a p))
  right_inv Q := Subtype.ext (Determinants.Grassmannian.replacementMinors_of_normalized a Q.val Q.property)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Plucker.ChartPoints.Grassmannian
