import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Linear Matrix Support -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearMatrixSupport.CM

noncomputable section

/-! Scalar support of matrix entries implies the same support for the
value of the linear operator on every vector. -/

theorem apply {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : R) (f g : (I → S) →ₗ[S] (I → S))
    (h : ∀ i j, a • (f (Pi.single j 1) i - g (Pi.single j 1) i) =
      f (Pi.single j 1) i - g (Pi.single j 1) i) (x : I → S) :
    a • (f x - g x) = f x - g x := by
  have he (F : (I → S) →ₗ[S] (I → S)) : F x = ∑ j, x j • F (Pi.single j 1) := by
    simp_rw [← F.map_smul]
    rw [← map_sum]
    congr 1
    funext i
    simp [Pi.single_apply]
  rw [he f, he g, ← Finset.sum_sub_distrib, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← smul_sub, smul_comm]
  congr 1
  funext i
  exact h i j

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LinearMatrixSupport.CM
