import OAI.Analysis.PDE.Green.CellCofactor

/-! The determinant-energy comparison on periodic spatial cells. -/

noncomputable section
namespace OAI.Analysis.PDE.Energy

open Set Matrix _root_.MeasureTheory OAI.Analysis.Calculus.Quaternion
  OAI.Analysis.PDE.Dirichlet OAI.Analysis.PDE.Green OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem cofactor_background_bound_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {B r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : OAI.Analysis.PDE.Green.CompatibleCellFaces c a b r (fun p x => u x * OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) p q) u p x))
    (hpos : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef) :
    cofactorBackgroundMass e ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) B u ≤
      (n : ℝ) * determinantMass e ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0})
        (fun y => B y + u y) u := by
  let A := OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y)
  have hb := (OAI.Analysis.PDE.Green.isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hXi := continuous_integrableOn_bounded hb (continuous_mass_integrand e (hB.add hu) hu.continuous)
  have hYi := continuous_integrableOn_bounded hb (continuous_background_integrand e hB hu)
  have hp (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) =
        (n : ℝ) * ((-u x) * OAI.LinearAlgebra.Moore.mooreDet n (A x)) -
          (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) := by
    have he : OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) +
        OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) = (n : ℝ) * OAI.LinearAlgebra.Moore.mooreDet n (A x) := by
      rw [← OAI.LinearAlgebra.Moore.mooreDifferential_add,
        ← hessian_sum e (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) x]
      exact OAI.LinearAlgebra.Moore.mooreDifferential_self n (A x)
    linear_combination (-u x) * he
  have hg := OAI.Analysis.PDE.Green.moore_cofactor_energy_cell_nonneg e c a b hab (hB.add hu)
    (hu.of_le (by norm_num)) hr hrne huz hface hpos
  change 0 ≤ ∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
    (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) at hg
  simp_rw [hp] at hg
  rw [integral_sub (hXi.const_mul _) hYi, integral_const_mul] at hg
  exact sub_nonneg.mp hg

theorem determinant_energy_comparison_of_background_bound {n s : ℕ}
    (e : Fin s → Quaternion ℝ) {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s)}
    (hS : MeasurableSet S) (hb : Bornology.IsBounded S)
    {B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hu0 : ∀ x ∈ S, u x ≤ 0)
    (hpos : ∀ x ∈ S, (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef)
    (hrank : ∀ x ∈ S, ∃ w : Fin (n + 2) → Quaternion ℝ, OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x = OAI.Analysis.Calculus.Quaternion.outer w)
    (hbound : cofactorBackgroundMass e S B u ≤ ((n : ℝ) + 2) *
      determinantMass e S (fun y => B y + u y) u) :
    ((n : ℝ) + 1) / ((n : ℝ) + 3) * determinantMass e S (fun y => B y + u y) u ≤
      determinantMass e S (fun y => B y + u y) u + determinantSegmentEnergy e S B u ∧
    determinantMass e S (fun y => B y + u y) u + determinantSegmentEnergy e S B u ≤
      determinantMass e S (fun y => B y + u y) u := by
  let X := determinantMass e S (fun y => B y + u y) u
  let Y := cofactorBackgroundMass e S B u
  have hX : 0 ≤ X := by
    apply setIntegral_nonneg hS
    intro x hx
    exact mul_nonneg (neg_nonneg.mpr (hu0 x hx))
      (OAI.LinearAlgebra.Moore.mooreDet_nonneg_of_complexify_posSemidef _ (hpos x hx))
  have hY : 0 ≤ Y := by
    apply setIntegral_nonneg hS
    intro x hx
    obtain ⟨w, hw⟩ := hrank x hx
    rw [hw]
    exact mul_nonneg (neg_nonneg.mpr (hu0 x hx))
      (OAI.LinearAlgebra.Moore.mooreDifferential_outer_nonneg _ w (hpos x hx))
  have hdim : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
  have hc := segment_energy_comparison (n + 1) hX hY (by rw [hdim]; exact hbound)
  dsimp only at hc
  rw [integral_segment] at hc
  have hn : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
  rw [hn] at hc
  change _ ≤ X + determinantSegmentEnergy e S B u ∧ determinantMass e S (fun y => B y + u y) u +
    determinantSegmentEnergy e S B u ≤ X
  rw [determinant_segment_energy_formula e hS hb hB hu hrank]
  have hn3 : (n : ℝ) + 1 + 2 = (n : ℝ) + 3 := by ring
  have hn2 : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
  rw [hn3, hn2] at hc
  simpa only [X, Y] using hc

theorem normalized_determinant_energy_comparison_cell {n s m : ℕ}
    (e : Fin s → Quaternion ℝ)
    (c : (Fin (n + 2) × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {B r u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : OAI.Analysis.PDE.Green.CompatibleCellFaces c a b r (fun p x => u x * OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) p q) u p x))
    (hu0 : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}, u x ≤ 0)
    (hpos : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef)
    (hrank : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      ∃ w : Fin (n + 2) → Quaternion ℝ, OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x = OAI.Analysis.Calculus.Quaternion.outer w)
    {lam : ℝ} (hlam : 0 < lam)
    (heq : ∀ x ∈ (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) = lam * μ x) :
    let S := (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}
    let X₀ := ∫ x in S, (-u x) * μ x
    let E := determinantSegmentEnergy e S B u / lam
    ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ X₀ + E ∧ X₀ + E ≤ X₀ := by
  have hb := (OAI.Analysis.PDE.Green.isBounded_euclidean_cell c a b).subset
    (inter_subset_left : ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) ⊆ _)
  have hS : MeasurableSet ((OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0}) :=
    (isClosed_Icc.preimage (OAI.Analysis.PDE.Green.euclideanCoordinates c).continuous).measurableSet.inter
      (isOpen_lt hr.continuous continuous_const).measurableSet
  have hbound := cofactor_background_bound_cell e c a b hab hB hu hr hrne huz hface hpos
  have h := determinant_energy_comparison_of_background_bound e hS hb hB hu hu0 hpos hrank
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hbound)
  rw [determinantMass_of_equation e hS _ _ _ lam heq] at h
  exact scaled_energy_comparison hlam h

end OAI.Analysis.PDE.Energy
