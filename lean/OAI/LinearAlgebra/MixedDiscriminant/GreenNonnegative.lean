import OAI.LinearAlgebra.MixedDiscriminant.GreenMoments
import OAI.LinearAlgebra.Moore.Rank.Mixed.CofactorPositive

noncomputable section
open Set Matrix _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise MatrixOrder ComplexOrder

namespace OAI.LinearAlgebra.MixedDiscriminant

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Energy OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

theorem mixedHessianCurrent_quadratic_nonneg {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hD : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef)
    (hB : (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (j : ℕ) (v : Fin n → Quaternion ℝ) :
    0 ≤ (OAI.Analysis.PDE.Dirichlet.quaternionForm (mixedHessianCurrent e B u j x) v).re := by
  apply (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (OAI.LinearAlgebra.Moore.mixedCofactor_isHermitian n _)).mp
  apply OAI.LinearAlgebra.Moore.mixedCofactor_posSemidef
  intro i
  split_ifs
  · exact hB
  · exact hD

theorem mixedHessianMass_succ_le_bounded {n s : ℕ} (hn : 0 < n)
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0)
    (hD : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef)
    (hBpos : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (j : ℕ) (hj : j < n) :
    OAI.Analysis.PDE.Energy.mixedHessianMass e S B u (j+1) ≤ OAI.Analysis.PDE.Energy.mixedHessianMass e S B u j := by
  apply sub_nonneg.mp
  rw [mixedHessianMass_sub_succ_bounded hn e hS hb hnull hB hu hz j hj]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
  apply setIntegral_nonneg hS.measurableSet
  intro x hx
  exact mixedHessianCurrent_quadratic_nonneg e x (hD x hx) (hBpos x hx) j _

theorem mixedHessianMass_succ_le_cell {n s m : ℕ} (hn : 0 < n)
    (e : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m+1))
    (a b : Fin (m+1) → ℝ) (hab : a ≤ b)
    {r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ x, r x = 0 → u x = 0) (hdata : OAI.Analysis.PDE.Green.RankCellData c a b r B u)
    (hD : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)).PosSemidef)
    (hBpos : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x)).PosSemidef)
    (j : ℕ) (hj : j < n) :
    OAI.Analysis.PDE.Energy.mixedHessianMass e ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u (j+1) ≤
      OAI.Analysis.PDE.Energy.mixedHessianMass e ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u j := by
  apply sub_nonneg.mp
  rw [mixedHessianMass_sub_succ_cell hn e c a b hab hB hu hr hrne hz hdata j hj]
  apply mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
  have hS : MeasurableSet ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    (isClosed_Icc.preimage (OAI.Analysis.PDE.Green.euclideanCoordinates c).continuous).measurableSet.inter
      (measurableSet_lt hr.continuous.measurable measurable_const)
  apply setIntegral_nonneg hS
  intro x hx
  exact mixedHessianCurrent_quadratic_nonneg e x (hD x hx) (hBpos x hx) j _

end OAI.LinearAlgebra.MixedDiscriminant
