import OAI.Analysis.PDE.Dirichlet.PureNormal

open Filter
open scoped Topology Matrix ComplexOrder MatrixOrder InnerProductSpace

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Calculus.Quaternion OAI.LinearAlgebra.Moore

theorem quaternionForm_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) Q) (z : Fin n → Q) :
    quaternionForm (A - B) z = quaternionForm A z - quaternionForm B z := by
  simp only [quaternionForm, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem quaternionForm_lower_of_shift {n : ℕ} (A : Matrix (Fin n) (Fin n) Q)
    (_ : A.IsHermitian) (r : ℝ)
    (hshift : (OAI.LinearAlgebra.Moore.complexify (A - r • (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef)
    (z : Fin n → Q) : r * (quaternionForm 1 z).re ≤ (quaternionForm A z).re := by
  have hH : (A - r • (1 : Matrix (Fin n) (Fin n) Q)).IsHermitian :=
    OAI.LinearAlgebra.Moore.isHermitian_of_complexify hshift.isHermitian
  have h := (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff hH).mp hshift z
  rw [quaternionForm_sub, quaternionForm_smul_matrix] at h
  change 0 ≤ (quaternionForm A z).re - r * (quaternionForm 1 z).re at h
  linarith

theorem quaternionGradient_of_normal {n s : ℕ} (e : Fin s → Q)
    {r : CoordinateSpace n s → ℝ} {x ν : CoordinateSpace n s} {k : ℝ}
    (h : fderiv ℝ r x = k • innerSL ℝ ν) :
    quaternionGradient e r x = k • OAI.Analysis.Calculus.Quaternion.gradientMap e ν := by
  funext a
  simp only [quaternionGradient, OAI.Analysis.Calculus.Quaternion.gradientMap, realGradient, h, smul_apply,
    innerSL_apply_apply, inner_coordinateVector, Pi.smul_apply, Finset.smul_sum,
    smul_smul, smul_eq_mul]

theorem quaternionPairing_smul_left {n : ℕ} (a : ℝ) (u v : Fin n → Q) :
    quaternionPairing (a • u) v = a • quaternionPairing u v := by
  simp [quaternionPairing, Finset.smul_sum]

/-- The strict tangential quaternionic lower bound is inherited from the
fixed defining function and the lower scalar boundary barrier. -/
theorem boundary_quaternionHessian_coercive {n : ℕ}
    {B₀ r u : CoordinateSpace n 4 → ℝ} {x ν : CoordinateSpace n 4}
    {a b r₀ k : ℝ} (hB₀ : ContDiff ℝ 2 B₀) (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u)
    (hrne : fderiv ℝ r x ≠ 0) (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x)
    (hnormal : fderiv ℝ r x = k • innerSL ℝ ν)
    (hb : 0 ≤ b) (hba : b ≤ a) (hr₀ : 0 ≤ r₀)
    (hbase : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x)).PosSemidef)
    (hconvex : (OAI.LinearAlgebra.Moore.complexify (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x - r₀ •
      (1 : Matrix (Fin n) (Fin n) Q))).PosSemidef)
    (z : Fin n → Q) (hz : quaternionPairing (OAI.Analysis.Calculus.Quaternion.gradientMap OAI.Analysis.Calculus.Quaternion.fourSlots ν) z = 0) :
    (b * r₀) * (quaternionForm 1 z).re ≤
      (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x) z).re := by
  have hz' : quaternionPairing (quaternionGradient OAI.Analysis.Calculus.Quaternion.fourSlots r x) z = 0 := by
    rw [quaternionGradient_of_normal OAI.Analysis.Calculus.Quaternion.fourSlots hnormal, quaternionPairing_smul_left, hz, smul_zero]
  have htan := boundary_quaternionHessian_tangent OAI.Analysis.Calculus.Quaternion.fourSlots hr hu hrne hzero hfactor z hz'
  have hR := quaternionForm_lower_of_shift (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x)
    (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hr.contDiffAt) r₀ hconvex z
  have hB := (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff
    (quaternionHessian_isHermitian OAI.Analysis.Calculus.Quaternion.fourSlots hB₀.contDiffAt)).mp hbase z
  have hI : 0 ≤ (quaternionForm (1 : Matrix (Fin n) (Fin n) Q) z).re := by
    apply (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff Matrix.isHermitian_one).mp
    · rw [OAI.LinearAlgebra.Moore.complexify_one]
      exact Matrix.PosSemidef.one
  have heq : quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots (fun y ↦ B₀ y + u y) x =
      quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x + quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots u x := by
    simpa only [one_smul] using quaternionHessian_add_smul OAI.Analysis.Calculus.Quaternion.fourSlots hB₀ hu 1 x
  rw [heq, quaternionForm_add, htan]
  change b * r₀ * (quaternionForm 1 z).re ≤
    (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots B₀ x) z).re +
      a * (quaternionForm (quaternionHessian OAI.Analysis.Calculus.Quaternion.fourSlots r x) z).re
  have ha : 0 ≤ a := hb.trans hba
  have h1 := mul_le_mul_of_nonneg_left hR ha
  have h2 := mul_le_mul_of_nonneg_right hba (mul_nonneg hr₀ hI)
  nlinarith

end OAI.Analysis.PDE.Dirichlet
