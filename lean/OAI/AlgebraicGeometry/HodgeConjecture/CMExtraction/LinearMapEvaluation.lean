import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Linear Map Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation.TestTransport

noncomputable section

/-! Evaluation of a linear operator is multiplication by the evaluated
matrix of its values on the standard basis. -/

open scoped Classical _root_.Matrix

theorem linearMap_evaluate {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (ρ : R →+* S) (f : (I → R) →ₗ[R] (I → R)) (x : I → R) :
    (fun i => ρ (f x i)) =
      (fun i j => ρ (f (Pi.single j 1) i)) *ᵥ (fun i => ρ (x i)) := by
  have he := LinearMap.toMatrix'_mulVec f x
  funext i
  exact (congrArg (fun y : I → R => ρ (y i)) he).symm.trans
    (RingHom.map_mulVec ρ (LinearMap.toMatrix' f) x i)

theorem linearMap_on_scalar_vectors {R S I : Type*} [CommRing R] [CommRing S]
    [Fintype I] [DecidableEq I] (ρ : R →+* S) (M : Matrix I I R)
    (f : (I → S) →ₗ[S] (I → S))
    (hf : ∀ i j, f (Pi.single j 1) i = ρ (M i j)) (x : I → R) :
    f (fun i => ρ (x i)) = fun i => ρ ((M *ᵥ x) i) := by
  have hm : LinearMap.toMatrix' f = M.map ρ := by
    ext i j
    exact hf i j
  rw [← LinearMap.toMatrix'_mulVec f, hm]
  funext i
  exact (RingHom.map_mulVec ρ M x i).symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LinearMapEvaluation.TestTransport
