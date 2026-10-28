import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-! # Scalar Conjugate Derivative -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarConjugateDerivative.TestTransport

noncomputable section

/-! Scalar conjugation changes the base point of a derivative and
leaves its linear map unchanged. -/

theorem fderiv_scalar_conjugate {K V W : Type*} [NontriviallyNormedField K]
    [NormedAddCommGroup V] [NormedSpace K V]
    [NormedAddCommGroup W] [NormedSpace K W]
    (F : V → W) (r : K) (hr : r ≠ 0) (x : V)
    (hF : DifferentiableAt K F (r • x)) :
    fderiv K (fun z => r⁻¹ • F (r • z)) x = fderiv K F (r • x) := by
  have h := ((hF.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul r)).const_smul r⁻¹).fderiv
  refine h.trans ?_
  ext z
  simp [smul_smul, hr]

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarConjugateDerivative.TestTransport
