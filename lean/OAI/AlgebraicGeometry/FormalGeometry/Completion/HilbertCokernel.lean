import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertAdditivity
import OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertTwist
import OAI.AlgebraicGeometry.FormalGeometry.Completion.PolynomialDifference
import OAI.AlgebraicGeometry.SheafCohomology.Projective.CoherentQuotientFiniteType

/-! # Hilbert Cokernel -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertCokernel

noncomputable section

/-! Actual coherent cokernels have the difference Hilbert polynomial.
A regular hyperplane map therefore lowers the polynomial degree. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits

namespace Construction

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {r : ℕ}
  {M N : (Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) K)).Modules}
  [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]

def projectiveCokernelHilbertPolynomial (f : M ⟶ N) (j : Fin (r + 1)) : Polynomial ℚ := by
  let := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel f
  let := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel f
  exact Projective.Numerics.Construction.projectiveHilbertPolynomial (cokernel f) j

theorem projectiveCokernelHilbertPolynomial_eq_sub [M.IsFiniteType]
    (f : M ⟶ N) [Mono f] (j : Fin (r + 1)) :
    projectiveCokernelHilbertPolynomial f j =
      Projective.Numerics.Construction.projectiveHilbertPolynomial N j - Projective.Numerics.Construction.projectiveHilbertPolynomial M j := by
  let := SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_cokernel f
  let := SheafCohomology.Projective.CoherentQuotientFiniteType.Scheme.Modules.isFiniteType_cokernel f
  let T := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hT : T.ShortExact := { exact := ShortComplex.cokernelSequence_exact f }
  have he := HilbertAdditivity.Construction.projectiveHilbertPolynomial_add_of_shortExact T hT j
  change Projective.Numerics.Construction.projectiveHilbertPolynomial N j =
    Projective.Numerics.Construction.projectiveHilbertPolynomial M j + projectiveCokernelHilbertPolynomial f j at he
  rw [he, add_sub_cancel_left]

variable (M) [M.IsFiniteType]

theorem projectiveHyperplaneCokernel_hilbertPolynomial (j : Fin (r + 1))
    (s : M ⟶ HilbertTwist.Construction.projectiveTwist M j 1) [Mono s] :
    projectiveCokernelHilbertPolynomial s j = PolynomialDifference.Construction.polynomialDifference (Projective.Numerics.Construction.projectiveHilbertPolynomial M j) := by
  rw [projectiveCokernelHilbertPolynomial_eq_sub, HilbertTwist.Construction.projectiveHilbertPolynomial_twist]
  rfl

theorem projectiveHyperplaneCokernel_hilbertDegree_le (j : Fin (r + 1))
    (s : M ⟶ HilbertTwist.Construction.projectiveTwist M j 1) [Mono s] :
    (projectiveCokernelHilbertPolynomial s j).natDegree ≤
      (Projective.Numerics.Construction.projectiveHilbertPolynomial M j).natDegree - 1 := by
  rw [projectiveHyperplaneCokernel_hilbertPolynomial]
  exact PolynomialDifference.Construction.polynomialDifference_natDegree_le _

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.HilbertCokernel
