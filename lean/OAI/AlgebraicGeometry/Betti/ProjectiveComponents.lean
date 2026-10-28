import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveComponent
import OAI.AlgebraicTopology.Cohomology.Singular.FiniteCoproduct
import OAI.AlgebraicGeometry.Betti.ProjectiveCohomology

/-! # Projective Components -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Actual cohomology decomposition of every smooth projective scheme

Smoothness supplies the local-domain theorem and hence the finite disjoint
integral-component decomposition. The analytic point homeomorphism and the
ordinary singular-cochain decomposition turn this into a canonical cohomology
equivalence, with coordinates given by the actual component inclusions.
Empty and disconnected presentations require no additional hypothesis.
-/

open _root_.CategoryTheory

variable (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)

/-- The ordinary topological spaces of the genuine integral components. -/
abbrev Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointSpaces (C : irreducibleComponents P.carrier) : TopCat :=
  Betti.Scheme.schemePointSpace (P.componentVariety C).toOver

/-- The established geometric decomposition as an isomorphism in `TopCat`. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentPointSpaceIso :
    TopCat.of (Σ C, P.componentPointSpaces C) ≅ Betti.Scheme.schemePointSpace P.toOver :=
  TopCat.isoOfHomeo P.componentPointsHomeomorph

/-- Ordinary singular cohomology is the product of the cohomology of the
actual integral components, without any presumed cohomological splitting. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv {R : Type} [Ring R] (M : ModuleCat R) (n : ℕ) :
    Betti.Scheme.schemeBetti M P.toOver n ≃ₗ[R]
      (∀ C : irreducibleComponents P.carrier, Betti.Scheme.schemeBetti M (P.componentVariety C).toOver n) :=
  ((AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyFunctor M n).mapIso
    P.componentPointSpaceIso.op).toLinearEquiv.trans
      (AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv P.componentPointSpaces M n)

/-- Each coordinate of the equivalence is the actual pullback along the
corresponding inclusion over the complex base. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_apply {R : Type} [Ring R] (M : ModuleCat R) (n : ℕ)
    (α : Betti.Scheme.schemeBetti M P.toOver n) (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv M n α C =
      Betti.Scheme.schemeBettiMap M n (P.componentInclusionOver C) α := by
  change AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv P.componentPointSpaces M n
    (AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback M
      P.componentPointSpaceIso.hom n α) C = _
  rw [AlgebraicTopology.Cohomology.Singular.FiniteCoproduct.singularSigmaCohomologyEquiv_apply]
  have hmap : TopCat.sigmaι P.componentPointSpaces C ≫
        P.componentPointSpaceIso.hom =
      ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPointsFunctor.map (P.componentInclusionOver C) := by
    ext x
    rfl
  have hp := AlgebraicTopology.Cohomology.Singular.Functor.singularCohomologyPullback_comp M
    (TopCat.sigmaι P.componentPointSpaces C)
    P.componentPointSpaceIso.hom n
  rw [hmap] at hp
  exact (ConcreteCategory.congr_hom hp α).symm

/-- Actual component restrictions jointly determine a cohomology class. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBetti_ext {R : Type} [Ring R] (M : ModuleCat R) (n : ℕ)
    {α β : Betti.Scheme.schemeBetti M P.toOver n}
    (h : ∀ C : irreducibleComponents P.carrier,
      Betti.Scheme.schemeBettiMap M n (P.componentInclusionOver C) α =
        Betti.Scheme.schemeBettiMap M n (P.componentInclusionOver C) β) : α = β := by
  apply (P.componentBettiEquiv M n).injective
  funext C
  simpa only [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_apply] using h C

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion of rational classes into ordinary complex cohomology is
exactly componentwise under this proved geometric decomposition. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_rationalInclusion (n : ℕ)
    (α : Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) P.toOver n)
    (C : irreducibleComponents P.carrier) :
    P.componentBettiEquiv (ModuleCat.of ℂ ℂ) n
        (Betti.Scheme.schemeBettiRationalInclusion P.toOver n α) C =
      (P.componentVariety C).rationalCohomologyInclusion n
        (P.componentBettiEquiv (ModuleCat.of ℚ ℚ) n α C) := by
  rw [Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_apply, Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.componentBettiEquiv_apply]
  exact (ConcreteCategory.congr_hom
    (Betti.Scheme.schemeBettiRationalInclusion_naturality (P.componentInclusionOver C) n) α).symm

end

end OAI.AlgebraicGeometry
