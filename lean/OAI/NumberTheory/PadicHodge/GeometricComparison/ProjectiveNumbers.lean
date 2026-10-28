import OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveAbelian
import OAI.NumberTheory.PadicHodge.GeometricComparison.BettiHalfDimension
import OAI.NumberTheory.PadicHodge.GeometricComparison.SubspaceBaseI
import OAI.NumberTheory.PadicHodge.GeometricComparison.AbelianDeRhamFiltration
import OAI.NumberTheory.PadicHodge.GeometricComparison.FirstHodgeNumber

/-! # Projective Numbers -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveNumbers

noncomputable section

/-! The local degree-one Hodge number follows from the given projective
presentation and its proved comparison, without a comparison assumption. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

private theorem projective_filtered_scalar_finrank
    {K L V W : Type*} [Field K] [Field L] [Algebra K L]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module L W]
    (e : L ⊗[K] V ≃ₗ[L] W) (P : Submodule K V) (Q : Submodule L W)
    (h : (P.baseChange L).map e.toLinearMap = Q) :
    Module.finrank L Q = Module.finrank K P := by
  rw [← h, e.finrank_map_eq, SubspaceBaseI.SubspaceBaseChange.finrank]

namespace AbelianH1Model

variable {K : Type} [Field K] [NumberField K]
  {q : ℕ} [Fact q.Prime] {jq : K →+* ℚ_[q]} (A : Geometry.AbelianH1Model K q jq)

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.projective_hodge_half_dimension (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom) :
    2 * Module.finrank ℚ_[q] (A.Fil 1) = Module.finrank ℚ_[q] A.DeRham := by
  let : Algebra K ℚ_[q] := jq.toAlgebra
  let : Algebra K ℂ := j.toAlgebra
  let : FiniteDimensional K A.AlgebraicDeRham :=
    A.algebraicDeRham_finite_of_projective_comparison j P
  let : FiniteDimensional ℂ (A.ComplexBetti j) := A.complexBetti_finiteDimensional j P
  let : FiniteDimensional ℂ ((A.smoothProjectiveFiber j P).complexCohomology 1) :=
    A.complexBetti_finiteDimensional j P
  obtain ⟨e, _, he⟩ := A.projectiveAlgebraicBettiComparison_exists j P
  have hl := projective_filtered_scalar_finrank A.localAlgebraicComparison (A.algebraicFiltration 1)
    (A.Fil 1) (A.localAlgebraicComparison_filtration 1)
  have hc := projective_filtered_scalar_finrank e (A.algebraicFiltration 1)
    (A.bettiFiltration j P 1) (he 1)
  have hld : Module.finrank ℚ_[q] A.DeRham = Module.finrank K A.AlgebraicDeRham :=
    A.localAlgebraicComparison.finrank_eq.symm.trans Module.finrank_baseChange
  have hcd : Module.finrank ℂ (A.ComplexBetti j) = Module.finrank K A.AlgebraicDeRham :=
    e.finrank_eq.symm.trans Module.finrank_baseChange
  have hs := BettiHalfDimension.BettiHodge.degreeOne_half_dimension (A.smoothProjectiveFiber j P)
  have hstep : A.bettiFiltration j P 1 = (A.smoothProjectiveFiber j P).pureBettiSubspace 1 0 := rfl
  rw [← hstep] at hs
  change 2 * Module.finrank ℂ (A.bettiFiltration j P 1) = Module.finrank ℂ (A.ComplexBetti j) at hs
  omega

theorem _root_.OAI.NumberTheory.PadicHodge.GeometricComparison.Geometry.AbelianH1Model.projective_hodge_number_twice (j : K →+* ℂ)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation (A.complexFiber j).scheme.left (A.complexFiber j).scheme.hom)
    [FiniteDimensional ℚ_[q] A.DeRham] :
    2 * A.finiteFiltration.tH = (Module.finrank ℚ_[q] A.DeRham : ℚ) := by
  rw [FirstHodgeNumber.FiltrationTransport.tH_h1 A.finiteFiltration (A.Fil_eq_top 0 le_rfl)
    (A.Fil_eq_bot 2 (by decide))]
  exact_mod_cast A.projective_hodge_half_dimension j P

end AbelianH1Model

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ProjectiveNumbers
