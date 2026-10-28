import OAI.Analysis.PDE.Concentration.EuclideanLattice
import OAI.Analysis.PDE.Green.CellFaces

noncomputable section
namespace OAI.Analysis.PDE.Concentration

open Set Matrix OAI.Analysis.PDE.Green OAI.Analysis.Calculus.Quaternion OAI.Analysis.PDE.Dirichlet OAI.LinearAlgebra.Moore

def latticeCellPeriod {ι : Type*} [Fintype ι] {m : ℕ} (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) : EuclideanSpace ℝ ι :=
  (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (Pi.single i (b i - a i)))

theorem lattice_face_translate {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (i : Fin (m + 1)) (y : Fin m → ℝ) :
    (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (b i) y)) =
      (OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (a i) y)) + latticeCellPeriod c L a b i := by
  rw [insertNth_eq_add_single i (a i) (b i) y, map_add, map_add]
  rfl

theorem latticeCoordinateField_periodic {ι : Type*} [Fintype ι] {m : ℕ}
    (c : ι ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (i : Fin (m + 1))
    (F : ι → EuclideanSpace ℝ ι → ℝ)
    (hF : ∀ j x, F j (x + latticeCellPeriod c L a b i) = F j x)
    (x : Fin (m + 1) → ℝ) :
    latticeCoordinateField c F (x + L (Pi.single i (b i - a i))) =
      latticeCoordinateField c F x := by
  funext j
  simp only [latticeCoordinateField, map_add]
  exact hF _ _

/-- Face hypotheses on the primitive functions: periodicity on genuine
lattice vectors, faces outside the fiber, or a zero test-function jet. -/
def CompatibleLatticePencilData {n s m : ℕ} (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (r B u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ) : Prop :=
  ∀ i,
    (∀ x, r (x + latticeCellPeriod c L a b i) = r x ∧
      B (x + latticeCellPeriod c L a b i) = B x ∧
      u (x + latticeCellPeriod c L a b i) = u x ∧
      v (x + latticeCellPeriod c L a b i) = v x) ∨
    (∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      0 ≤ r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (b i) y))) ∧
      0 ≤ r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (a i) y)))) ∨
    (∀ y ∈ Icc (a ∘ i.succAbove) (b ∘ i.succAbove),
      v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (b i) y))) = 0 ∧
      fderiv ℝ v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (b i) y))) = 0 ∧
      v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (a i) y))) = 0 ∧
      fderiv ℝ v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L (i.insertNth (a i) y))) = 0)

theorem pencil_compatible_lattice_faces {n s m : ℕ} (e : Fin s → Quaternion ℝ)
    (c : (Fin n × Fin s) ≃ Fin (m + 1))
    (L : (Fin (m + 1) → ℝ) ≃L[ℝ] (Fin (m + 1) → ℝ))
    (a b : Fin (m + 1) → ℝ) (r B u v : OAI.Analysis.PDE.Dirichlet.CoordinateSpace n s → ℝ)
    (hdata : CompatibleLatticePencilData c L a b r B u v) (t : ℝ) :
    CompatibleLatticeFaces c L a b r (OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
      (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
        (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v) := by
  intro i y hy
  let F := OAI.Analysis.PDE.Green.secondGreenFlux OAI.Analysis.PDE.Dirichlet.coordinateVector
    (fun p q x => OAI.Analysis.Calculus.Quaternion.realCoefficients e (OAI.LinearAlgebra.Moore.mooreCofactor n
      (OAI.Analysis.PDE.Dirichlet.quaternionHessian e (fun y => B y + t * u y) x)) p q) u v
  rcases hdata i with hp | ho | hv
  · left
    apply parallelepiped_face_match_of_periodic L (latticeCoordinateField c F)
      (fun z => r ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm z)) i (a i) (b i)
    · apply latticeCoordinateField_periodic c L a b i F
      intro j x
      apply OAI.Analysis.PDE.Green.cofactor_secondGreenFlux_periodic_add e _ u v (latticeCellPeriod c L a b i)
      · intro x
        rw [(hp x).2.1, (hp x).2.2.1]
      · exact fun x => (hp x).2.2.1
      · exact fun x => (hp x).2.2.2
    · intro x
      simp only [map_add]
      exact (hp _).1
  · exact Or.inr (Or.inl (ho y hy))
  · right
    right
    obtain ⟨hvu, hdvu, hvl, hdvl⟩ := hv y hy
    have hz (z : Fin (m + 1) → ℝ)
        (hzv : v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L z)) = 0)
        (hzdv : fderiv ℝ v ((OAI.Analysis.PDE.Green.euclideanCoordinates c).symm (L z)) = 0) :
        linearPiola L (latticeCoordinateField c F) z = 0 := by
      have hf : latticeCoordinateField c F (L z) = 0 := by
        funext j
        exact OAI.Analysis.PDE.Green.secondGreenFlux_zero_of_test_jet _ _ _ _ _ hzv hzdv _
      simp only [linearPiola, Function.comp_apply, hf, map_zero]
    exact ⟨congrFun (hz _ hvu hdvu) i, congrFun (hz _ hvl hdvl) i⟩

end OAI.Analysis.PDE.Concentration
