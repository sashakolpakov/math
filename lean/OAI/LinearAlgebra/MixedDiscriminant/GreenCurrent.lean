import OAI.LinearAlgebra.MixedDiscriminant.GreenLinear

noncomputable section
open Set Matrix _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

namespace OAI.LinearAlgebra.MixedDiscriminant

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

/-- The energy identity is linear in the conserved current. In particular,
it applies to the finite polarization of a Hessian cofactor. -/
theorem current_energy_bounded {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 2 u)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in S, (OAI.Analysis.PDE.Dirichlet.quaternionForm (A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have h := OAI.Analysis.PDE.Green.quaternion_current_green_bounded e hS hb hnull hA hdiv
    (hu.of_le (by norm_num)) hu hz
  have he (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient u x q) =
      (OAI.Analysis.PDE.Dirichlet.quaternionForm (A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
    simp_rw [mul_assoc]
    exact OAI.Analysis.PDE.Green.realCoefficients_quadratic _ e (OAI.Analysis.PDE.Dirichlet.realGradient u x)
  simp_rw [he] at h
  simp_rw [neg_mul]
  rw [integral_neg,h,neg_neg]

theorem current_energy_bounded_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x b, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) b = 0)
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 2 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hherm : ∀ x ∈ S, (A x).IsHermitian)
    (hpos : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (A x)).PosSemidef) :
    0 ≤ ∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  rw [current_energy_bounded e hS hb hnull hA hdiv hu hz]
  apply setIntegral_nonneg hS.measurableSet
  intro x hx
  exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (hherm x hx)).mp (hpos x hx) _

theorem current_energy_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {A : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → Matrix (Fin n) (Fin n) (Quaternion ℝ)}
    (hA : ContDiff ℝ 1 A)
    (hdiv : ∀ x j, OAI.Analysis.Calculus.Quaternion.strongDivergence e
      (fun p => fderiv ℝ A x (OAI.Analysis.PDE.Dirichlet.coordinateVector p)) j = 0)
    {r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 2 u) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ x, r x = 0 → u x = 0)
    (hface : OAI.Analysis.PDE.Green.CompatibleCellFaces c a b r (fun p x => u x *
      OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q) u p x)) :
    (∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (-u x) * OAI.LinearAlgebra.Moore.realTrace (A x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
        (OAI.Analysis.PDE.Dirichlet.quaternionForm (A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have h := OAI.Analysis.PDE.Green.quaternion_current_first_green_cell e c a b hab hA hdiv
    (hu.of_le (by norm_num)) hu hr hrne hz hface
  have he (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      (∑ p, ∑ q, OAI.Analysis.Calculus.Quaternion.realCoefficients e (A x) p q *
        OAI.Analysis.PDE.Dirichlet.realGradient u x p * OAI.Analysis.PDE.Dirichlet.realGradient u x q) =
      (OAI.Analysis.PDE.Dirichlet.quaternionForm (A x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
    simp_rw [mul_assoc]
    exact OAI.Analysis.PDE.Green.realCoefficients_quadratic _ e (OAI.Analysis.PDE.Dirichlet.realGradient u x)
  simp_rw [he] at h
  simp_rw [neg_mul]
  rw [integral_neg,h,neg_neg]

end OAI.LinearAlgebra.MixedDiscriminant
