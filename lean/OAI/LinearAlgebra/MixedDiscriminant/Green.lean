import OAI.LinearAlgebra.MixedDiscriminant.GreenHessian
import OAI.LinearAlgebra.MixedDiscriminant.GreenCurrent

noncomputable section
open Set Matrix _root_.MeasureTheory
open scoped Matrix.Norms.Elementwise ComplexOrder MatrixOrder

namespace OAI.LinearAlgebra.MixedDiscriminant

open OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore OAI.Analysis.PDE.Green

theorem mixed_cofactor_energy_bounded {n s : ℕ} (e : Fin s → Quaternion ℝ)
    {S : Set (OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    (hnull : volume (frontier S) = 0)
    (ψ : Fin (n - 1) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hψ : ∀ i, ContDiff ℝ 3 (ψ i))
    {u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 2 u)
    (hz : ∀ x ∈ frontier S, u x = 0) :
    (∫ x in S, (-u x) * OAI.LinearAlgebra.Moore.realTrace
      (OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x) * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in S, (OAI.Analysis.PDE.Dirichlet.quaternionForm
        (OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x))
        (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re :=
  current_energy_bounded e hS hb hnull (contDiff_mixedCofactor_hessian e ψ hψ)
    (mixedCofactor_hessian_divergence e ψ hψ) hu hz

theorem mixed_cofactor_energy_cell {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ) (hab : a ≤ b)
    (ψ : Fin (n - 1) → OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hψ : ∀ i, ContDiff ℝ 3 (ψ i))
    {r u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ} (hu : ContDiff ℝ 2 u) (hr : ContDiff ℝ 2 r)
    (hrne : ∀ x ∈ OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b, r x = 0 → fderiv ℝ r x ≠ 0)
    (hz : ∀ x, r x = 0 → u x = 0)
    (hface : OAI.Analysis.PDE.Green.CompatibleCellFaces c a b r (fun p x => u x *
      OAI.Analysis.PDE.Green.realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x)) p q) u p x)) :
    (∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
      (-u x) * OAI.LinearAlgebra.Moore.realTrace
        (OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x) * OAI.Analysis.PDE.Dirichlet.quaternionHessian e u x)) =
      ∫ x in (OAI.Analysis.PDE.Green.euclideanCoordinates c ⁻¹' Icc a b) ∩ {x | r x < 0},
        (OAI.Analysis.PDE.Dirichlet.quaternionForm (OAI.LinearAlgebra.Moore.mixedCofactor n (fun i => OAI.Analysis.PDE.Dirichlet.quaternionHessian e (ψ i) x))
          (OAI.Analysis.PDE.Dirichlet.quaternionGradient e u x)).re :=
  current_energy_cell e c a b hab (contDiff_mixedCofactor_hessian e ψ hψ)
    (mixedCofactor_hessian_divergence e ψ hψ) hu hr hrne hz hface

end OAI.LinearAlgebra.MixedDiscriminant
