import OAI.AlgebraicTopology.Kunneth.RestrictedSimplexIntegration
import OAI.AlgebraicTopology.Products.Cup

/-! # Simplex Form Cochain -/

namespace OAI.AlgebraicTopology.Kunneth.SimplexFormCochain

noncomputable section

/-! Actual integrals of restricted forms on every face of the standard simplicial simplex. -/

set_option backward.isDefEq.respectTransparency false

open _root_.CategoryTheory Opposite OAI.AlgebraicTopology.Products.Cup
open scoped Simplicial

namespace Constructions

def simplexFormCochain (n p : ℕ) :
    RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p →ₗ[ℂ]
      (Cohomology.Singular.Basic.simplicialCochains Δ[n] (ModuleCat.of ℂ ℂ)).X p :=
  (Cohomology.Singular.Coefficients.degreewiseFunctionIso Δ[n] (ModuleCat.of ℂ ℂ) p).toLinearEquiv.symm.toLinearMap.comp
    (LinearMap.pi fun s : Δ[n] _⦋p⦌ =>
      (RestrictedSimplexIntegration.Constructions.simplexIntegral p).comp (SimplexFormMaps.Constructions.simplexFormPullback (SSet.stdSimplex.objEquiv s) p))

@[simp] theorem simplexFormCochain_evaluation (n p : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p) (s : Δ[n] _⦋p⦌) :
    Cohomology.Singular.Coefficients.simplicialEvaluation Δ[n] (ModuleCat.of ℂ ℂ) s (simplexFormCochain n p a) =
      RestrictedSimplexIntegration.Constructions.simplexIntegral p (SimplexFormMaps.Constructions.simplexFormPullback (SSet.stdSimplex.objEquiv s) p a) := by
  rw [← Cohomology.Singular.Coefficients.degreewiseFunctionIso_hom_apply]
  change ((Cohomology.Singular.Coefficients.degreewiseFunctionIso Δ[n] (ModuleCat.of ℂ ℂ) p).toLinearEquiv
    ((Cohomology.Singular.Coefficients.degreewiseFunctionIso Δ[n] (ModuleCat.of ℂ ℂ) p).toLinearEquiv.symm _)) s = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem simplexFormCochain_d (n p : ℕ) (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p) :
    (Cohomology.Singular.Basic.simplicialCochains Δ[n] (ModuleCat.of ℂ ℂ)).d p (p + 1) (simplexFormCochain n p a) =
      simplexFormCochain n (p + 1) (RestrictedForms.Constructions.restrictedFormD (SimplexFormDomain.Constructions.coordinateSimplex_uniqueDiffOn n) p a) := by
  apply Products.Cup.cochain_ext Δ[n] (ModuleCat.of ℂ ℂ)
  intro s
  rw [Cohomology.Singular.Formulas.evaluation_coboundary_apply, simplexFormCochain_evaluation,
    ← SimplexFormMaps.Constructions.simplexFormPullback_d, RestrictedSimplexIntegration.Constructions.simplexIntegral_stokes]
  apply Finset.sum_congr rfl
  intro j _
  rw [simplexFormCochain_evaluation, ← SimplexFormMaps.Constructions.simplexFormPullback_comp]
  rfl

theorem simplexFormCochain_pullback {m n : ℕ} (f : ⦋m⦌ ⟶ ⦋n⦌) (p : ℕ)
    (a : RestrictedForms.Constructions.RestrictedForm (SimplexFormDomain.Constructions.coordinateSimplex n) p) :
    (Cohomology.Singular.Functor.simplicialPullback (ModuleCat.of ℂ ℂ) (SSet.stdSimplex.map f)).f p
      (simplexFormCochain n p a) =
        simplexFormCochain m p (SimplexFormMaps.Constructions.simplexFormPullback f p a) := by
  apply Products.Cup.cochain_ext Δ[m] (ModuleCat.of ℂ ℂ)
  intro s
  rw [Cohomology.Singular.Formulas.evaluation_pullback_apply, simplexFormCochain_evaluation,
    simplexFormCochain_evaluation, ← SimplexFormMaps.Constructions.simplexFormPullback_comp]
  rfl

end Constructions

end

end OAI.AlgebraicTopology.Kunneth.SimplexFormCochain
