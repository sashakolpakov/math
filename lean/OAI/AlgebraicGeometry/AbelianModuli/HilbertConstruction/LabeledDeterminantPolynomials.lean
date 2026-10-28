import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveFrame.Polynomials

/-! # Labeled Determinant Polynomials -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantPolynomials

noncomputable section

/-! Actual maximal minors of the matrix of labeled vectors, including
their behavior under evaluation, coordinate changes, and point rescaling. -/
open scoped BigOperators Classical
universe u v
variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] {r m : ℕ}

def labeledDeterminant (σ : Fin r → Fin m) (v : Fin m → Fin r → R) : R :=
  Matrix.det (fun i j => v (σ j) i)

def labeledDeterminantPolynomial (R : Type u) [CommRing R]
    (σ : Fin r → Fin m) : MvPolynomial (Fin m × Fin r) R :=
  labeledDeterminant σ (fun i j => MvPolynomial.X (i, j))

theorem labeledDeterminant_eq_basis (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) :
    labeledDeterminant σ v = (Pi.basisFun R (Fin r)).det (fun j => v (σ j)) := by
  rw [Pi.basisFun_det_apply]
  exact Matrix.det_transpose _

theorem labeledDeterminant_map (f : R →+* A)
    (σ : Fin r → Fin m) (v : Fin m → Fin r → R) :
    f (labeledDeterminant σ v) =
      labeledDeterminant σ (fun i j => f (v i j)) := by
  exact f.map_det _

theorem labeledDeterminantPolynomial_eval [Algebra R A]
    (σ : Fin r → Fin m) (v : Fin m → Fin r → A) :
    MvPolynomial.aeval (fun ij : Fin m × Fin r => v ij.1 ij.2)
      (labeledDeterminantPolynomial R σ) = labeledDeterminant σ v := by
  unfold labeledDeterminantPolynomial
  change (MvPolynomial.aeval (fun ij : Fin m × Fin r => v ij.1 ij.2)).toRingHom
    (labeledDeterminant σ (fun i j => MvPolynomial.X (i, j))) = _
  rw [labeledDeterminant_map]
  congr 1
  funext i j
  exact MvPolynomial.aeval_X (fun ij : Fin m × Fin r => v ij.1 ij.2) (i, j)

theorem labeledDeterminant_rescale (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (c : Fin m → R) :
    labeledDeterminant σ (fun i j => c i * v i j) =
      (∏ j, c (σ j)) * labeledDeterminant σ v := by
  exact Matrix.det_mul_row (fun j => c (σ j)) (fun i j => v (σ j) i)

theorem labeledDeterminant_linear (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (T : (Fin r → R) →ₗ[R] (Fin r → R)) :
    labeledDeterminant σ (fun i => T (v i)) =
      LinearMap.det T * labeledDeterminant σ v := by
  rw [labeledDeterminant_eq_basis, labeledDeterminant_eq_basis]
  exact (Pi.basisFun R (Fin r)).det_comp T (fun j => v (σ j))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LabeledDeterminantPolynomials
