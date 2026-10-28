import OAI.AlgebraicGeometry.Comparison.Betti.Holomorphic.StandardFunctionSheaf
import OAI.AlgebraicGeometry.Comparison.Betti.MultivariablePolynomialGerms

/-! # Polynomial Holomorphic Sections -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.PolynomialHolomorphicSections.AnalyticLocal

noncomputable section

/-! Actual polynomial functions define standard holomorphic sections,
whose section germs are the original polynomial germ evaluation. -/

open _root_.TopologicalSpace Set Filter
open scoped _root_.Topology _root_.Manifold ContDiff

variable {n : ℕ}

def functionSectionOfDifferentiable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (U : Opens E) (F : E → ℂ) (hF : DifferentiableOn ℂ F U) :
    Holomorphic.FunctionPure.holomorphicFunctions U :=
  ⟨fun y => F y, by
    have hs := Geometry.ComplexTorus.RiemannProjectivity.HolomorphicContourF.Constructions.HolomorphicDerivative.contDiffOn_infty_of_differentiableOn U.isOpen hF
    apply hs.congr
    intro y hy
    exact Holomorphic.CoefficientMem.openCoefficientExtension_apply U (fun y => F y) ⟨y, hy⟩⟩

theorem polynomial_eval_differentiable (P : MvPolynomial (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => MvPolynomial.eval x P) := by
  intro x
  obtain ⟨F, hFmap, U, hU, hx, hF⟩ := (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x P).property
  have he := Germ.coe_eq.mp (hFmap.trans (MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_val x P))
  exact (hF.differentiableAt (hU.mem_nhds hx)).congr_of_eventuallyEq he.symm

def polynomialCoefficientSection (P : MvPolynomial (Fin n) ℂ) (U : Opens (Fin n → ℂ)) :
    Holomorphic.FunctionPure.holomorphicFunctions U :=
  functionSectionOfDifferentiable U (fun x => MvPolynomial.eval x P)
    (polynomial_eval_differentiable P).differentiableOn

def polynomialHolomorphicSection (P : MvPolynomial (Fin n) ℂ) (U : Opens (Fin n → ℂ)) :
    C^∞⟮𝓘(ℂ, Fin n → ℂ), U; 𝓘(ℂ), ℂ⟯ :=
  Holomorphic.StandardFunctionSheaf.AnalyticLocal.holomorphicFunctionContMDiffEquiv (Fin n → ℂ) U (polynomialCoefficientSection P U)

theorem polynomialHolomorphicSection_apply (P : MvPolynomial (Fin n) ℂ)
    (U : Opens (Fin n → ℂ)) (x : U) : polynomialHolomorphicSection P U x = MvPolynomial.eval x P := rfl

theorem polynomialCoefficientSection_germ (P : MvPolynomial (Fin n) ℂ) (U : Opens (Fin n → ℂ))
    (x : Fin n → ℂ) (hx : x ∈ U) :
    Holomorphic.SectionGerms.AnalyticLocal.holomorphicSectionGerm U x hx (polynomialCoefficientSection P U) = MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap x P := by
  apply Subtype.ext
  rw [MultivariablePolynomialGerms.AnalyticLocal.mvPolynomialGermMap_val]
  apply Germ.coe_eq.mpr
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact Holomorphic.CoefficientMem.openCoefficientExtension_apply U (polynomialCoefficientSection P U).val ⟨y, hy⟩

end

end OAI.AlgebraicGeometry.Comparison.Betti.PolynomialHolomorphicSections.AnalyticLocal
