import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.CoordinateMonomials

/-! # Chart Denominators -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.ChartDenominators

noncomputable section

/-! A single monomial contains the frame discriminant and one nonzero
normalized coordinate of every point. Its principal open supports all
the corresponding affine coordinate charts. -/
open scoped BigOperators Classical
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {r m : ℕ}

def frameDiscriminantExponent (σ : Fin r → Fin m) (e : Fin m) :
    (Fin r → Fin m) → ℕ :=
  Pi.single σ 1 + ∑ k, Pi.single (Function.update σ k e) 1

def frameChartExponent (σ : Fin r → Fin m) (e : Fin m) (c : Fin m → Fin r) :
    (Fin r → Fin m) → ℕ :=
  frameDiscriminantExponent σ e + ∑ z, CoordinateExponents.frameCoordinateExponent σ e z (c z)

theorem frameDiscriminantExponent_monomial (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (e : Fin m) :
    Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (frameDiscriminantExponent σ e) =
      ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin r)) (fun j => v (σ j)) (v e) := by
  have hsingle (j : Fin r → Fin m) :
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (Pi.single j 1) = LabeledDeterminantPolynomials.labeledDeterminant j v := by
    simp [Balanced.MonomialAlgebra.exponentMonomial, Pi.single_apply]
  simp only [frameDiscriminantExponent, Balanced.MonomialAlgebra.exponentMonomial_add, MonomialFiniteSums.exponentMonomial_sum, hsingle]
  simp only [CoordinateMonomials.labeledDeterminant_update_eq_basis, ProjectiveFrame.Discriminant.projectiveFrameDiscriminant]
  rw [LabeledDeterminantPolynomials.labeledDeterminant_eq_basis]
  congr!

theorem frameChartExponent_monomial (σ : Fin r → Fin m)
    (v : Fin m → Fin r → R) (e : Fin m) (c : Fin m → Fin r) :
    Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (frameChartExponent σ e c) =
      ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun R (Fin r)) (fun j => v (σ j)) (v e) *
        ∏ z, DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun R (Fin r))
          (fun j => v (σ j)) (v e) (v z) (c z) := by
  simp only [frameChartExponent, Balanced.MonomialAlgebra.exponentMonomial_add, MonomialFiniteSums.exponentMonomial_sum,
    frameDiscriminantExponent_monomial, CoordinateMonomials.frameCoordinateExponent_linearMap]

theorem frameCoordinateExponent_le_chart (σ : Fin r → Fin m)
    (e z : Fin m) (c : Fin m → Fin r) :
    CoordinateExponents.frameCoordinateExponent σ e z (c z) ≤ frameChartExponent σ e c := by
  intro τ
  have hz := Finset.single_le_sum
    (fun j _ => Nat.zero_le (CoordinateExponents.frameCoordinateExponent σ e j (c j) τ)) (Finset.mem_univ z)
  change CoordinateExponents.frameCoordinateExponent σ e z (c z) τ ≤
    frameDiscriminantExponent σ e τ + (∑ j, CoordinateExponents.frameCoordinateExponent σ e j (c j)) τ
  simpa only [Finset.sum_apply] using hz.trans (Nat.le_add_left _ _)

theorem frameDiscriminantExponent_le_chart (σ : Fin r → Fin m)
    (e : Fin m) (c : Fin m → Fin r) :
    frameDiscriminantExponent σ e ≤ frameChartExponent σ e c := by
  intro τ
  exact Nat.le_add_right _ _

theorem frame_exists_nonvanishing_chart {K : Type u} [Field K]
    (v : Fin m → Fin r → K) (hv : ∀ z, v z ≠ 0)
    (σ : Fin r → Fin m) (e : Fin m)
    (hframe : IsUnit (ProjectiveFrame.Discriminant.projectiveFrameDiscriminant (Pi.basisFun K (Fin r))
      (fun j => v (σ j)) (v e))) :
    ∃ c : Fin m → Fin r,
      Balanced.MonomialAlgebra.exponentMonomial (fun τ => LabeledDeterminantPolynomials.labeledDeterminant τ v) (frameChartExponent σ e c) ≠ 0 := by
  let f := DeterminantFrameLinearMap.determinantFrameLinearMap (Pi.basisFun K (Fin r)) (fun j => v (σ j)) (v e)
  have hinj : Function.Injective f := (DeterminantFrameLinearMap.determinantFrameLinearMap_bijective _ _ _ hframe).1
  have hcoord (z : Fin m) : ∃ k : Fin r, f (v z) k ≠ 0 := by
    by_contra! h
    apply hv z
    apply hinj
    exact (funext h).trans (map_zero f).symm
  choose c hc using hcoord
  refine ⟨c, ?_⟩
  rw [frameChartExponent_monomial]
  exact mul_ne_zero (isUnit_iff_ne_zero.mp hframe)
    (Finset.prod_ne_zero_iff.mpr (fun z _ => hc z))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Frame.ChartDenominators
