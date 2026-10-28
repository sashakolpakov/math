import OAI.AlgebraicGeometry.ComplexPoints.Analytic.ProjectiveVarietyRealization
import OAI.AlgebraicGeometry.Foundations.Scheme.TranscendenceDimension
import OAI.AlgebraicGeometry.Betti.Scheme
import OAI.AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses
import OAI.Analysis.DifferentialForms.Manifold.CovectorAction
import OAI.Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence

/-! # Projective Cohomology -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Cohomology and pure forms on an actual projective variety

All spaces here are formed from the algebraic variety itself. In particular,
the topology, manifold structure, and dimension are the proved realization,
not additional fields of a bundle. This module assembles the two cohomology
theories and their concrete meanings. The global comparison between them and
the algebraic cycle class map must still be constructed separately.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold ContDiff

/-- Rational singular cohomology of the actual complex-point space. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomology (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) : ModuleCat ℚ :=
  Betti.Scheme.schemeBetti (ModuleCat.of ℚ ℚ) V.toOver n

/-- Complex singular cohomology of that same topological space. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexCohomology (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) : ModuleCat ℂ :=
  Betti.Scheme.schemeBetti (ModuleCat.of ℂ ℂ) V.toOver n

/-- Extension of singular coefficients along the actual inclusion of rationals
in the complex numbers, viewed as a rational linear map. -/
def Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomologyInclusion (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.rationalCohomology n ⟶
      (ModuleCat.restrictScalars (algebraMap ℚ ℂ)).obj (V.complexCohomology n) :=
  Betti.Scheme.schemeBettiRationalInclusion V.toOver n

theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.rationalCohomologyInclusion_injective (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    Function.Injective (V.rationalCohomologyInclusion n) :=
  Betti.Scheme.schemeBettiRationalInclusion_injective V.toOver n

/-- De Rham cohomology of genuine global smooth complex-valued forms on the
derived real manifold. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamCohomology (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) : ModuleCat ℂ :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamCohomology V.analyticModel V.analyticSpace n

/-- The standard closed-forms modulo exact-forms presentation. -/
def Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamQuotientIso (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    V.deRhamCohomology n ≅
      ModuleCat.of ℂ (Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotient V.analyticModel V.analyticSpace n) :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormQuotientIso V.analyticModel V.analyticSpace n

/-- The actual cohomology class of a closed global differential form. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.deRhamClass (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (n : ℕ) :
    Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace n →ₗ[ℂ] V.deRhamCohomology n :=
  Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldDeRhamFormClass V.analyticModel V.analyticSpace n

/-- Classes admitting a closed representative of the indicated pure type. -/
abbrev Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.pureDeRhamSubspace (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ) :
    Submodule ℂ (V.deRhamCohomology (p + q)) :=
  AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.manifoldPureDeRhamImage V.analyticModel V.analyticSpace p q

/-- Membership means existence of a closed form with the standard
inverse-character action on the actual complex tangent spaces. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_pureDeRhamSubspace_iff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (α : V.deRhamCohomology (p + q)) :
    α ∈ V.pureDeRhamSubspace p q ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (p + q),
        Analysis.DifferentialForms.Manifold.CovectorAction.HasTangentBidegree V.analyticModel V.analyticSpace p q
          (form.val : Analysis.DifferentialForms.Manifold.Algebra.RawManifoldForm V.analyticModel V.analyticSpace (p + q)) ∧
        V.deRhamClass (p + q) form = α := by
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff]
  apply exists_congr
  intro form
  exact and_congr (Analysis.DifferentialForms.Manifold.CovectorAction.hasManifoldBidegree_iff_tangentBidegree _) Iff.rfl

/-- The same membership statement written literally using the real exterior
power of the tangent bundle and its complex-valued dual, as in the supplied
statement. The displayed powers have the contragredient signs. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.mem_pureDeRhamSubspace_iff_exteriorDual
    (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p q : ℕ)
    (α : V.deRhamCohomology (p + q)) :
    α ∈ V.pureDeRhamSubspace p q ↔
      ∃ form : Analysis.DifferentialForms.Manifold.ManifoldDeRham.manifoldClosedForms V.analyticModel V.analyticSpace (p + q),
        (∀ (x : V.analyticSpace) (z : ℂˣ),
          (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.tangentExteriorCovectorEquiv x (p + q) (form.val.val x)).comp
              (exteriorPower.map (p + q)
                (Analysis.DifferentialForms.Manifold.ComplexAction.complexTangentScalarMap x (↑(z⁻¹) : ℂ)).toLinearMap) =
            ((z : ℂ) ^ (-(p : ℤ)) * (star (z : ℂ)) ^ (-(q : ℤ))) •
              Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.tangentExteriorCovectorEquiv x (p + q) (form.val.val x)) ∧
        V.deRhamClass (p + q) form = α := by
  rw [AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.mem_manifoldPureDeRhamImage_iff]
  apply exists_congr
  intro form
  exact and_congr (Analysis.DifferentialForms.Manifold.ExteriorCovectorEquivalence.hasManifoldBidegree_iff_exteriorDual_action _) Iff.rfl

/-- The analytic complex dimension is the ordinary transcendence dimension
of the variety's function field over its specified complex base. -/
theorem Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety.complexDimension_eq_transcendenceDimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) :
    V.complexDimension = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap :=
  (Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_eq_functionFieldDifferentialDimension V.structureMap).symm

end

end OAI.AlgebraicGeometry
