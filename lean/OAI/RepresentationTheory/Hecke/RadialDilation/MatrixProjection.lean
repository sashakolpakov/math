import Mathlib

/-! # Matrix Projection -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.MatrixProjection.Realization

noncomputable section

/-! Matrix compatibility with a module inclusion over a projected scalar ring. -/

open scoped _root_.Matrix

theorem matrix_mul_projected_vector {R K ι : Type*} [CommSemiring R] [CommSemiring K]
    [Fintype ι] (P : R →+* K) (I : K →+ R)
    (hI : ∀ a x, a * I x = I (P a * x)) (A : Matrix ι ι R) (x : ι → K) :
    A *ᵥ (fun i => I (x i)) = fun i => I ((A.map P *ᵥ x) i) := by
  funext i
  change (∑ j, A i j * I (x j)) = I (∑ j, P (A i j) * x j)
  rw [map_sum]
  exact Finset.sum_congr rfl (fun j _ => hI (A i j) (x j))

end

end OAI.RepresentationTheory.Hecke.RadialDilation.MatrixProjection.Realization
