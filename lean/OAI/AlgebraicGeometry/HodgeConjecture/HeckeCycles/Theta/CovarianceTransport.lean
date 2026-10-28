import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! # Covariance Transport -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.CovarianceTransport.CM

/-! Transport literal theta covariance along equality of the input and
the entire period map, retaining its derivative. -/

theorem apply {𝕜 V X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (T : V → X → (X →L[𝕜] 𝕜)) (a b c : V) (p q : X → X) (ha : a = b) (hp : p = q)
    (x : X) (h : (T b (q x)).comp (fderiv 𝕜 q x) = T c x) :
    (T a (p x)).comp (fderiv 𝕜 p x) = T c x := by
  subst a
  subst p
  exact h

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.CovarianceTransport.CM
