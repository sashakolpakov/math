import OAI.AlgebraicTopology.FundamentalClass.DuffyDomain
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Determinant

/-! # Duffy Derivative -/

namespace OAI.AlgebraicTopology.FundamentalClass.DuffyDerivative.IntegrationConstruction.Duffy

noncomputable section

/-! Integration: the Jacobian of the cube-to-simplex map is positive in the interior.
The calculation uses the triangular dependence of the barycentric coordinates. -/

open Set
open scoped ContDiff

theorem front_coordinate_line {d : ℕ} (t : Fin d → ℝ) (i j : Fin d)
    (hij : i ≤ j) (s : ℝ) :
    DuffyDomain.IntegrationConstruction.Duffy.front d (t + s • Pi.single j 1) i =
      (t i + if i = j then s else 0) * ∏ k ∈ Finset.Iio i, (1 - t k) := by
  rw [DuffyDomain.IntegrationConstruction.Duffy.front, DeRham.Comparison.DuffyCoordinates.Duffy.coordinates_castSucc]
  have hp : ∏ k ∈ Finset.Iio i, (1 - (t + s • Pi.single j (1 : ℝ) : Fin d → ℝ) k) =
      ∏ k ∈ Finset.Iio i, (1 - t k) := by
    apply Finset.prod_congr rfl
    intro k hk
    have hkj : k ≠ j := ne_of_lt (lt_of_lt_of_le (Finset.mem_Iio.mp hk) hij)
    simp [Ne.symm hkj]
  rw [hp]
  by_cases h : i = j <;> simp [h]

theorem fderiv_front_basis_of_le {d : ℕ} (t : Fin d → ℝ) (i j : Fin d) (hij : i ≤ j) :
    (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t (Pi.single j 1)) i =
      if i = j then ∏ k ∈ Finset.Iio i, (1 - t k) else 0 := by
  have hline : HasDerivAt (fun s : ℝ => t + s • Pi.single j (1 : ℝ)) (Pi.single j 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ))).const_add t
  have hf := (DuffyDomain.IntegrationConstruction.Duffy.front_contDiff d).differentiable (by simp) |>.differentiableAt (x := t)
  have hcomp : HasDerivAt (fun s : ℝ => DuffyDomain.IntegrationConstruction.Duffy.front d (t + s • Pi.single j 1))
      (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t (Pi.single j 1)) 0 := by
    have hbase : HasFDerivAt (DuffyDomain.IntegrationConstruction.Duffy.front d) (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t)
        (t + (0 : ℝ) • Pi.single j (1 : ℝ)) := by simpa using hf.hasFDerivAt
    exact hbase.comp_hasDerivAt 0 hline
  have hc : HasDerivAt (fun s : ℝ => DuffyDomain.IntegrationConstruction.Duffy.front d (t + s • Pi.single j 1) i)
      ((fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t (Pi.single j 1)) i) 0 :=
    (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt 0 hcomp
  simp_rw [front_coordinate_line t i j hij] at hc
  by_cases h : i = j
  · simp only [ite_eq_left h] at hc ⊢
    have hd : HasDerivAt (fun s : ℝ =>
        (t i + s) * ∏ k ∈ Finset.Iio i, (1 - t k))
        (∏ k ∈ Finset.Iio i, (1 - t k)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (t i)).mul_const
        (∏ k ∈ Finset.Iio i, (1 - t k))
    exact hc.unique hd
  · simp only [ite_eq_right h, add_zero] at hc ⊢
    exact hc.unique (hasDerivAt_const 0 _)

def frontJacobian (d : ℕ) (t : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin d)) (Pi.basisFun ℝ (Fin d))
    (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t).toLinearMap

theorem frontJacobian_apply {d : ℕ} (t : Fin d → ℝ) (i j : Fin d) :
    frontJacobian d t i j = (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t (Pi.single j 1)) i := by
  simp [frontJacobian]

theorem frontJacobian_lowerTriangular (d : ℕ) (t : Fin d → ℝ) :
    (frontJacobian d t).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  rw [frontJacobian_apply, fderiv_front_basis_of_le t i j hij'.le,
    ite_eq_right (ne_of_lt hij')]

theorem fderiv_front_det (d : ℕ) (t : Fin d → ℝ) :
    (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t).toLinearMap.det =
      ∏ i : Fin d, ∏ k ∈ Finset.Iio i, (1 - t k) := by
  rw [← LinearMap.det_toMatrix (Pi.basisFun ℝ (Fin d))]
  change (frontJacobian d t).det = _
  rw [Matrix.det_of_isLowerTriangular _ (frontJacobian_lowerTriangular d t)]
  apply Finset.prod_congr rfl
  intro i _
  rw [frontJacobian_apply, fderiv_front_basis_of_le t i i le_rfl, ite_eq_left rfl]

theorem fderiv_front_det_pos (d : ℕ) (t : Fin d → ℝ) (ht : t ∈ DuffyDomain.IntegrationConstruction.Duffy.cubeInterior d) :
    0 < (fderiv ℝ (DuffyDomain.IntegrationConstruction.Duffy.front d) t).toLinearMap.det := by
  rw [fderiv_front_det]
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro k _
  exact sub_pos.mpr (ht k).2

end

end OAI.AlgebraicTopology.FundamentalClass.DuffyDerivative.IntegrationConstruction.Duffy
