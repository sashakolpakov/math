import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Linear Action Matrices -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearActionMatrices.TestTransport

noncomputable section

/-! Matrix coordinates of a continuous linear action, with the
coordinate identities checked before specializing the coefficient ring. -/

open scoped Classical _root_.Matrix
open _root_.Matrix

variable {R G J : Type*} [CommRing R] [Group G] [Fintype J] [DecidableEq J]
  (ρ : G →* ((J → R) ≃ₗ[R] (J → R)))

def linearActionMatrix (g : G) : Matrix J J R := fun i j => ρ g (Pi.single j 1) i

omit [Fintype J] in
theorem linearActionMatrix_apply (g : G) (i j : J) :
    linearActionMatrix ρ g i j = ρ g (Pi.single j 1) i := rfl

theorem linearActionMatrix_mulVec (g : G) (x : J → R) :
    linearActionMatrix ρ g *ᵥ x = ρ g x :=
  LinearMap.toMatrix'_mulVec (ρ g).toLinearMap x

omit [Fintype J] in
theorem linearActionMatrix_one : linearActionMatrix ρ 1 = 1 := by
  unfold linearActionMatrix
  rw [map_one]
  change (fun (i j : J) => (Pi.single j (1 : R) : J → R) i) = (1 : Matrix J J R)
  funext i j
  simp only [Pi.single_apply, Matrix.one_apply]

omit [Fintype J] in
theorem linearActionMatrix_continuous [TopologicalSpace R] [TopologicalSpace G]
    (hρ : Continuous (fun z : G × (J → R) => ρ z.1 z.2)) :
    Continuous (linearActionMatrix ρ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (continuous_apply i).comp (hρ.comp (continuous_id.prodMk continuous_const))

theorem matrix_column_from_vector (A : Matrix J J R) (x y : J → R) (j : J)
    (hx : x = Pi.single j 1) (h : A *ᵥ x = y) (i : J) : A i j = y i := by
  rw [hx, Matrix.mulVec_single_one] at h
  exact congr_fun h i

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearActionMatrices.TestTransport
