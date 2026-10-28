import OAI.LinearAlgebra.MixedDiscriminant.Green
import OAI.LinearAlgebra.MixedDiscriminant.Adjacent
import OAI.LinearAlgebra.Moore.Rank.Mixed.Pairing
import OAI.Analysis.PDE.Energy.Rank.Energy.Moments
import OAI.Analysis.PDE.Green.RankEnergyCellFaces

noncomputable section
open Set Matrix _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise

namespace OAI.LinearAlgebra.MixedDiscriminant

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Energy OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

theorem mixed_hessian_difference {n s : ℕ} (hn : 0 < n) (e : Fin s → Quaternion ℝ)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 2 B) (hu : ContDiff ℝ 2 u)
    (j : ℕ) (hj : j < n) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n => if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) -
    OAI.LinearAlgebra.Moore.mixedMoore n (fun i : Fin n => if i.val < j+1 then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
      else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) =
    (n : ℝ)⁻¹ * OAI.LinearAlgebra.Moore.realTrace (OAI.LinearAlgebra.Moore.mixedCofactor n
      (fun i : Fin (n-1) => if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
        else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  cases n with
  | zero => omega
  | succ n =>
      have hH : OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x - OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x =
          OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x := by
        rw [OAI.Analysis.PDE.Energy.hessian_sum e hB hu x,add_sub_cancel_left]
      rw [OAI.LinearAlgebra.Moore.mixedMoore_adjacent _ _ j hj,hH,OAI.LinearAlgebra.Moore.mixedCofactor_pairing _ _
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian_isHermitian e hu.contDiffAt)]
      have hn0 : (n+1 : ℝ) ≠ 0 := by positivity
      simp only [Nat.cast_succ]
      rw [inv_mul_cancel_left₀ hn0]
      rfl

def mixedHessianCurrent {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (j : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    Matrix (Fin n) (Fin n) (Quaternion ℝ) :=
  OAI.LinearAlgebra.Moore.mixedCofactor n (fun i : Fin (n-1) => if i.val < j then OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x
    else OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y+u y) x)

theorem mixedHessianCurrent_eq {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (j : ℕ) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    mixedHessianCurrent e B u j x = OAI.LinearAlgebra.Moore.mixedCofactor n
      (fun i : Fin (n-1) => OAI.Analysis.PDE.Dirichlet.quaternionHessian e
        (if i.val < j then B else fun y => B y+u y) x) := by
  unfold mixedHessianCurrent
  congr 1
  funext i
  split_ifs <;> rfl

theorem mixedHessianCurrent_energy_bounded {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0) (j : ℕ) :
    (∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.realTrace (mixedHessianCurrent e B u j x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in S, (OAI.Analysis.PDE.Dirichlet.quaternionForm (mixedHessianCurrent e B u j x)
        (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  simp_rw [mixedHessianCurrent_eq]
  apply mixed_cofactor_energy_bounded e hS hb hnull _ _ (hu.of_le (by norm_num)) hz
  intro i
  split_ifs
  · exact hB
  · exact hB.add hu

theorem mixedHessianCurrent_energy_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m+1)) (a b : Fin (m+1) → ℝ) (hab : a ≤ b)
    {r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ x, r x = 0 → u x = 0) (hdata : OAI.Analysis.PDE.Green.RankCellData c a b r B u) (j : ℕ) :
    (∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (-u x) * OAI.LinearAlgebra.Moore.realTrace (mixedHessianCurrent e B u j x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
        (OAI.Analysis.PDE.Dirichlet.quaternionForm (mixedHessianCurrent e B u j x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have hf := OAI.Analysis.PDE.Green.rankCellData_compatible_faces e c a b
    (fun D A => OAI.LinearAlgebra.Moore.mixedCofactor n (fun i : Fin (n-1) => if i.val < j then A else D))
    r B u hdata
  change OAI.Analysis.PDE.Green.CompatibleCellFaces c a b r (fun p x => u x *
    OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e
      (mixedHessianCurrent e B u j x) p q) u p x) at hf
  simp_rw [mixedHessianCurrent_eq] at hf ⊢
  apply mixed_cofactor_energy_cell e c a b hab _ _ (hu.of_le (by norm_num)) hr hrne hz hf
  intro i
  split_ifs
  · exact hB
  · exact hB.add hu

theorem mixedHessianMass_sub_succ_eq_integral {n s : ℕ} (hn : 0 < n)
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (j : ℕ) (hj : j < n) :
    OAI.Analysis.PDE.Energy.mixedHessianMass e S B u j - OAI.Analysis.PDE.Energy.mixedHessianMass e S B u (j+1) =
      (n : ℝ)⁻¹ * ∫ x in S, (-u x) *
        OAI.LinearAlgebra.Moore.realTrace (mixedHessianCurrent e B u j x * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  rw [OAI.Analysis.PDE.Energy.mixedHessianMass,OAI.Analysis.PDE.Energy.mixedHessianMass,← integral_sub
    (OAI.Analysis.PDE.Energy.integrable_mixed_hessian_integrand e hb hB hu j)
    (OAI.Analysis.PDE.Energy.integrable_mixed_hessian_integrand e hb hB hu (j+1))]
  simp_rw [← mul_sub,mixed_hessian_difference hn e (hB.of_le (by norm_num))
    (hu.of_le (by norm_num)) j hj]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  dsimp [mixedHessianCurrent]
  ring

theorem mixedHessianMass_sub_succ_bounded {n s : ℕ} (hn : 0 < n)
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)}
    (hS : IsOpen S) (hb : Bornology.IsBounded S) (hnull : volume (frontier S) = 0)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hz : ∀ x ∈ frontier S, u x = 0) (j : ℕ) (hj : j < n) :
    OAI.Analysis.PDE.Energy.mixedHessianMass e S B u j - OAI.Analysis.PDE.Energy.mixedHessianMass e S B u (j+1) =
      (n : ℝ)⁻¹ * ∫ x in S, (OAI.Analysis.PDE.Dirichlet.quaternionForm (mixedHessianCurrent e B u j x)
        (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  rw [mixedHessianMass_sub_succ_eq_integral hn e hb hB hu j hj,
    mixedHessianCurrent_energy_bounded e hS hb hnull hB hu hz j]

theorem mixedHessianMass_sub_succ_cell {n s m : ℕ} (hn : 0 < n)
    (e : Fin s → Quaternion ℝ) (c : (Fin n × Fin s) ≃ Fin (m+1))
    (a b : Fin (m+1) → ℝ) (hab : a ≤ b)
    {r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ x, r x = 0 → u x = 0) (hdata : OAI.Analysis.PDE.Green.RankCellData c a b r B u)
    (j : ℕ) (hj : j < n) :
    OAI.Analysis.PDE.Energy.mixedHessianMass e ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u j -
      OAI.Analysis.PDE.Energy.mixedHessianMass e ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u (j+1) =
      (n : ℝ)⁻¹ * ∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
        (OAI.Analysis.PDE.Dirichlet.quaternionForm (mixedHessianCurrent e B u j x) (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re := by
  have hb : Bornology.IsBounded ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    (OAI.Analysis.PDE.Green.isBounded_euclidean_cell c a b).subset Set.inter_subset_left
  rw [mixedHessianMass_sub_succ_eq_integral hn e hb hB hu j hj,
    mixedHessianCurrent_energy_cell e c a b hab hB hu hr hrne hz hdata j]

end OAI.LinearAlgebra.MixedDiscriminant
