import OAI.Analysis.PDE.Concentration.Lattice.Quaternion
import OAI.Analysis.PDE.Energy.CellComparison

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix _root_.MeasureTheory OAI.Analysis.PDE.Energy OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

theorem moore_cofactor_energy_lattice_nonneg {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {ψ r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hψ : ContDiff ℝ 3 ψ)
    (hu : ContDiff ℝ 2 u) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleLatticeFaces c L a b r (fun p x => u x * OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)) p q) u p x))
    (hpos : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x)).PosSemidef) :
    0 ≤ ∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0}, (-u x) *
      OAI.LinearAlgebra.Moore.mooreDifferential n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e ψ x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) := by
  rw [moore_cofactor_energy_lattice e c L a b hab hψ hu hr hrne huz hface]
  apply setIntegral_nonneg ((measurableSet_euclideanLatticeCell c L a b).inter
    (isOpen_lt hr.continuous continuous_const).measurableSet)
  intro x hx
  exact (OAI.LinearAlgebra.Moore.complexify_posSemidef_iff (OAI.LinearAlgebra.Moore.mooreCofactor_isHermitian n _)).mp
    (OAI.LinearAlgebra.Moore.mooreCofactor_posSemidef _ (hpos x hx)) _

theorem cofactor_background_bound_lattice {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {B r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleLatticeFaces c L a b r (fun p x => u x * OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor n (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) p q) u p x))
    (hpos : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef) :
    OAI.Analysis.PDE.Energy.cofactorBackgroundMass e (euclideanLatticeCell c L a b ∩ {x | r x < 0}) B u ≤
      (n : ℝ) * OAI.Analysis.PDE.Energy.determinantMass e (euclideanLatticeCell c L a b ∩ {x | r x < 0})
        (fun y => B y + u y) u := by
  let A := OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y)
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : (euclideanLatticeCell c L a b ∩ {x | r x < 0}) ⊆ _)
  have hXi := OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (OAI.Analysis.PDE.Energy.continuous_mass_integrand e (hB.add hu) hu.continuous)
  have hYi := OAI.Analysis.PDE.Energy.continuous_integrableOn_bounded hb (OAI.Analysis.PDE.Energy.continuous_background_integrand e hB hu)
  have hp (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
      (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) =
        (n : ℝ) * ((-u x) * OAI.LinearAlgebra.Moore.mooreDet n (A x)) -
          (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) := by
    have he : OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x) +
        OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) = (n : ℝ) * OAI.LinearAlgebra.Moore.mooreDet n (A x) := by
      rw [← OAI.LinearAlgebra.Moore.mooreDifferential_add,
        ← OAI.Analysis.PDE.Energy.hessian_sum e (hB.of_le (by norm_num)) (hu.of_le (by norm_num)) x]
      exact OAI.LinearAlgebra.Moore.mooreDifferential_self n (A x)
    linear_combination (-u x) * he
  have hg := moore_cofactor_energy_lattice_nonneg e c L a b hab (hB.add hu)
    (hu.of_le (by norm_num)) hr hrne huz hface hpos
  change 0 ≤ ∫ x in euclideanLatticeCell c L a b ∩ {x | r x < 0},
    (-u x) * OAI.LinearAlgebra.Moore.mooreDifferential n (A x) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x) at hg
  simp_rw [hp] at hg
  rw [integral_sub (hXi.const_mul _) hYi, integral_const_mul] at hg
  exact sub_nonneg.mp hg

/-- The normalized determinant-energy comparison, with the manuscript's
constants, on an arbitrary spatial lattice cell. -/
theorem normalized_determinant_energy_comparison_lattice {n s m : ℕ}
    (e : Fin s → Quaternion ℝ)
    (c : (Fin (n + 2) × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    {B r u μ : OAI.Analysis.PDE.Dirichlet.CoordinateSpace (n + 2) s → ℝ} (hB : ContDiff ℝ 3 B) (hu : ContDiff ℝ 3 u)
    (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ euclideanLatticeCell c L a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (huz : ∀ x, r x = 0 → u x = 0)
    (hface : CompatibleLatticeFaces c L a b r (fun p x => u x * OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mooreCofactor (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)) p q) u p x))
    (hu0 : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0}, u x ≤ 0)
    (hpos : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0},
      (OAI.LinearAlgebra.Moore.complexify (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x)).PosSemidef)
    (hrank : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0},
      ∃ w : Fin (n + 2) → Quaternion ℝ, OAI.Analysis.PDE.Dirichlet.quaternionHessian e B x = OAI.Analysis.Calculus.Quaternion.outer w)
    {lam : ℝ} (hlam : 0 < lam)
    (heq : ∀ x ∈ euclideanLatticeCell c L a b ∩ {x | r x < 0},
      OAI.LinearAlgebra.Moore.mooreDet (n + 2) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + u y) x) = lam * μ x) :
    let S := euclideanLatticeCell c L a b ∩ {x | r x < 0}
    let X₀ := ∫ x in S, (-u x) * μ x
    let E := OAI.Analysis.PDE.Energy.determinantSegmentEnergy e S B u / lam
    ((n : ℝ) + 1) / ((n : ℝ) + 3) * X₀ ≤ X₀ + E ∧ X₀ + E ≤ X₀ := by
  have hb := (isBounded_euclideanLatticeCell c L a b).subset
    (inter_subset_left : (euclideanLatticeCell c L a b ∩ {x | r x < 0}) ⊆ _)
  have hS : MeasurableSet (euclideanLatticeCell c L a b ∩ {x | r x < 0}) :=
    (measurableSet_euclideanLatticeCell c L a b).inter
      (isOpen_lt hr.continuous continuous_const).measurableSet
  have hbound := cofactor_background_bound_lattice e c L a b hab hB hu hr hrne huz hface hpos
  have h := OAI.Analysis.PDE.Energy.determinant_energy_comparison_of_background_bound e hS hb hB hu hu0 hpos hrank
    (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hbound)
  rw [OAI.Analysis.PDE.Energy.determinantMass_of_equation e hS _ _ _ lam heq] at h
  exact OAI.Analysis.PDE.Energy.scaled_energy_comparison hlam h

end OAI.Analysis.PDE.Concentration
