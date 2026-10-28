import OAI.Analysis.PDE.Green.EuclideanCell
import OAI.Analysis.PDE.Green.Periodicity

/-! Primitive periodicity and test-function jets imply face cancellation. -/

noncomputable section
namespace OAI.Analysis.PDE.Green

open Set Matrix OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

def cellPeriod {ι : Type*} [Fintype ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : EuclideanSpace ℝ ι :=
  (euclideanCoordinates c).symm (Pi.single i (b i - a i))

theorem cell_face_translate {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ)
    (i : Fin (m + 1)) (y : Fin m → ℝ) :
    (euclideanCoordinates c).symm (i.insertNth (b i) y) =
      (euclideanCoordinates c).symm (i.insertNth (a i) y) + cellPeriod c a b i := by
  rw [insertNth_eq_add_single i (a i) (b i) y, map_add]
  rfl

/-- Each pair of faces is either periodic for the primitive data, outside the
sublevel, or has vanishing test-function value and first derivative. -/
def CompatiblePencilData {n s m : ℕ} (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (a b : Fin (m + 1) → ℝ) (r B u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) : Prop :=
  ∀ i,
    (∀ x, r (x + cellPeriod c a b i) = r x ∧
      B (x + cellPeriod c a b i) = B x ∧
      u (x + cellPeriod c a b i) = u x ∧
      v (x + cellPeriod c a b i) = v x) ∨
    (∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (b i) y)) ∧
      0 ≤ r ((euclideanCoordinates c).symm (i.insertNth (a i) y))) ∨
    (∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      v ((euclideanCoordinates c).symm (i.insertNth (b i) y)) = 0 ∧
      fderiv ℝ v ((euclideanCoordinates c).symm (i.insertNth (b i) y)) = 0 ∧
      v ((euclideanCoordinates c).symm (i.insertNth (a i) y)) = 0 ∧
      fderiv ℝ v ((euclideanCoordinates c).symm (i.insertNth (a i) y)) = 0)

theorem pencil_compatible_faces {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1)) (a b : Fin (m + 1) → ℝ)
    (r B u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) (hdata : CompatiblePencilData c a b r B u v)
    (t : ℝ) :
    CompatibleCellFaces c a b r (secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v) := by
  intro i y hy
  rcases hdata i with hp | ho | hv
  · left
    constructor
    · rw [cell_face_translate c a b i y]
      exact (hp _).1
    · rw [cell_face_translate c a b i y]
      apply cofactor_secondGreenFlux_periodic_add e _ u v (cellPeriod c a b i)
      · intro x
        rw [(hp x).2.1, (hp x).2.2.1]
      · exact fun x => (hp x).2.2.1
      · exact fun x => (hp x).2.2.2
  · exact Or.inr (Or.inl (ho y hy))
  · right
    right
    obtain ⟨hvu, hdvu, hvl, hdvl⟩ := hv y hy
    exact ⟨secondGreenFlux_zero_of_test_jet _ _ _ _ _ hvu hdvu _,
      secondGreenFlux_zero_of_test_jet _ _ _ _ _ hvl hdvl _⟩

end OAI.Analysis.PDE.Green
