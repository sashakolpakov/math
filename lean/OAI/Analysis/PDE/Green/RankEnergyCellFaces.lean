import OAI.Analysis.PDE.Green.CellFaces
import OAI.Analysis.PDE.Green.CellFirstGreen

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

/-- A cell direction is periodically identified, or both of its faces lie
outside the open domain. No artificial zero value is imposed on periodic faces. -/
def RankCellData {n s m : ℕ} (c : (Fin n × Fin s) ≃ Fin (m+1))
    (a b : Fin (m+1) → ℝ) (r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) : Prop :=
  ∀ i, (∀ x, r (x + cellPeriod c a b i) = r x ∧
    B (x + cellPeriod c a b i) = B x ∧ u (x + cellPeriod c a b i) = u x) ∨
    (∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (b i) y)) ∧
      0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (a i) y)))

theorem hessian_function_firstFlux_periodic_add {n s : ℕ} (e : Fin s → Quaternion ℝ)
    (Φ : Matrix (Fin n) (Fin n) (Quaternion ℝ) →
      Matrix (Fin n) (Fin n) (Quaternion ℝ) → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (w : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s)
    (hB : ∀ x, B (x+w) = B x) (hu : ∀ x, u (x+w) = u x)
    (p : Fin n × Fin s) (x : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s) :
    u (x+w) * realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun z => B z + u z) y) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B y)) p q)
      u p (x+w) =
    u x * realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun z => B z + u z) y) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B y)) p q)
      u p x := by
  have hsum : ∀ y, (B (y+w)+u (y+w)) = B y+u y := fun y => by rw [hB, hu]
  simp only [realFlux, hu, quaternionHessian_periodic_add e (fun z => B z + u z) w hsum,
    quaternionHessian_periodic_add e B w hB, fderiv_periodic_add u w hu]

theorem rankCellData_compatible_faces {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m+1)) (a b : Fin (m+1) → ℝ)
    (Φ : Matrix (Fin n) (Fin n) (Quaternion ℝ) →
      Matrix (Fin n) (Fin n) (Quaternion ℝ) → Matrix (Fin n) (Fin n) (Quaternion ℝ))
    (r B u : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hdata : RankCellData c a b r B u) :
    CompatibleCellFaces c a b r (fun p x => u x * realFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q y => OAI.Analysis.Calculus.Quaternion.realCoefficients e
        (Φ (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun z => B z + u z) y) (OAI.Analysis.PDE.Dirichlet.quaternionHessian e B y)) p q)
      u p x) := by
  intro i y hy
  rcases hdata i with hp | ho
  · left
    constructor
    · rw [cell_face_translate c a b i y]
      exact (hp _).1
    · rw [cell_face_translate c a b i y]
      exact hessian_function_firstFlux_periodic_add e Φ B u (cellPeriod c a b i)
        (fun x => (hp x).2.1) (fun x => (hp x).2.2) _ _
  · exact Or.inr (Or.inl (ho y hy))

end OAI.Analysis.PDE.Green
