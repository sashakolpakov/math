import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.Matching

/-! # Reference Theta -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceTheta.CM

noncomputable section

/-! Construct a reference-level theta class by pulling back the original
class along the actual quotient map. Deep reference levels lie inside a
fixed source level by the proved lattice comparison. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  (B : GeometricSource.CM.BallDatum E) (Λ : Submodule ℤ (GeometricSource.CM.Vec E))
  (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)

/-- A cofinal set of reference levels refines the original base level. -/
theorem reference_level_bound (Nbase : ℕ) (hNbase : 0 < Nbase) :
    let Bref := CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2
    ∃ M : ℕ, 0 < M ∧ Nbase ∣ M ∧ ∀ R : ℕ, M ∣ R →
      ∀ g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E, Bref.principalLevel R g → B.principalLevel Nbase g := by
  let Bref := CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2
  obtain ⟨M, hM, hbase, hlevels⟩ := ReferenceDatum.CM.source_levels_refine_reference E Bref B.lattice
    ⟨B.lattice_fg, B.lattice_full, B.lattice_stable⟩ Nbase Nbase hNbase hNbase
  refine ⟨M, hM, hbase, ?_⟩
  intro R hR g hg
  exact (ReferenceDatum.CM.principalLevel_iff E B Nbase g).mpr (hlevels R hR g hg)

variable {B Λ hΛ}

/-- The same theta derivative is pulled back using only the actual
holomorphic covering maps and their derivative chain rule. -/
theorem represents_reference_pullback
    {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (π : B.Domain → X.analyticSpace) (ρ : B.Domain → Y.analyticSpace)
    (hρ : MDifferentiable 𝓘(ℂ, GeometricSource.CM.BallChart) 𝓘(ℂ, Y.analyticModel) ρ)
    (f : C(Y.analyticSpace, X.analyticSpace))
    (hf : ContMDiff 𝓘(ℂ, Y.analyticModel) 𝓘(ℂ, X.analyticModel) ∞ f)
    (hcomp : ∀ z, f (ρ z) = π z)
    (form : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hform : GeometricSource.CM.RepresentsTheta E L φ X π form) :
    GeometricSource.CM.RepresentsTheta E L φ Y ρ (AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback.pureClosedManifoldFormsPullback f hf 1 0 form) := by
  intro z ξ
  have heq : (f : Y.analyticSpace → X.analyticSpace) ∘ ρ = π := funext hcomp
  have hd : mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, X.analyticModel) π z =
      (mfderiv 𝓘(ℝ, Y.analyticModel) 𝓘(ℝ, X.analyticModel) f (ρ z)).comp
        (mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, Y.analyticModel) ρ z) := by
    rw [← heq]
    exact mfderiv_comp z
      ((Analysis.DifferentialForms.Manifold.Holomorphic.contMDiff_real_of_complex hf).mdifferentiable (by decide) (ρ z))
      (Theta.Matching.CM.mdifferentiableAt_real (hρ z))
  change form.val.val.val (f (ρ z))
    (fun _ : Fin 1 => mfderiv 𝓘(ℝ, Y.analyticModel) 𝓘(ℝ, X.analyticModel) f (ρ z)
      (mfderiv 𝓘(ℝ, GeometricSource.CM.BallChart) 𝓘(ℝ, Y.analyticModel) ρ z ξ)) = _
  rw [hcomp]
  convert hform z ξ using 1
  rw [hd]
  rfl

/-- A reference cover at a refining level carries an actual closed theta
form and its canonical rational-complexified cohomology class. -/
theorem reference_theta_from_source
    {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (N R : ℕ)
    (π : B.Domain → X.analyticSpace)
    (ρ : (CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2).Domain → Y.analyticSpace)
    (hπ : B.IsBallCover N X π)
    (hρ : (CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover R Y ρ)
    (hcontain : ∀ g : GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E,
      (CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2).principalLevel R g → B.principalLevel N g)
    (form : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hform : GeometricSource.CM.RepresentsTheta E L φ X π form)
    (θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθ : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θ =
      (X.deRhamBettiIso 1).hom (X.deRhamClass 1 form.val)) :
    ∃ (f : C(Y.analyticSpace, X.analyticSpace))
      (_hf : ContMDiff 𝓘(ℂ, Y.analyticModel) 𝓘(ℂ, X.analyticModel) ∞ f),
      Function.Surjective f ∧ (∀ z, f (ρ z) = π z) ∧
      ∃ formY : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0,
        GeometricSource.CM.RepresentsTheta E L φ Y ρ formY ∧
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1
          ((AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ θ) =
            (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 formY.val) := by
  let Bref := CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2
  obtain ⟨f, hf, hsurj, hcomp⟩ := CoverFactor.CM.map_of_principal_containment E Bref B.lattice
    B.lattice_fg B.lattice_full B.lattice_stable N R Y X ρ π hρ hπ hcontain
  have hhol := CoverDerivative.CM.descended_map_mdifferentiable ρ π hρ.2.1
    hρ.2.2.1 hρ.2.2.2.1 hρ.2.2.2.2.1 hπ.2.2.2.1 f hcomp
  have hsmooth := (CoverSmooth.CM.quotient_map_contMDiff Bref R Y X ρ hρ f hhol).1
  let fc : C(Y.analyticSpace, X.analyticSpace) := ⟨f, hf⟩
  refine ⟨fc, hsmooth, hsurj, hcomp,
    AlgebraicTopology.DeRham.Comparison.ManifoldPureClassesPullback.pureClosedManifoldFormsPullback fc hsmooth 1 0 form,
    represents_reference_pullback E L φ X Y π ρ hρ.2.2.2.1 fc hsmooth hcomp form hform, ?_⟩
  rw [AnalyticPullback.CM.complexification_pullback, hθ,
    AnalyticPullback.CM.pullback_form_class fc hsmooth 1]
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceTheta.CM
