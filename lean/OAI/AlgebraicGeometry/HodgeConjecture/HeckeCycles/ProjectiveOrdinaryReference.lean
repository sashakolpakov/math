import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ZeroMatchedReference
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.ProjectiveLevel
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectivePreparedReduction

/-! # Projective Ordinary Reference -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectiveOrdinaryReference.CM.OrdinaryReference

noncomputable section

/-! The actual source family has a matched reference component whose
principal PEL level preserves the line of its prescribed original theta input and whose
ordinary-prime construction retains that input’s spherical bound and frames. The level,
reference class, and all deeper restrictions are constructed from the
full named prerequisites. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceTheta.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM

universe u v

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E]

theorem source_family_has_prepared_zero_reference
    (d : Gal(E/ℚ) → Bool) (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ)
    (h_CongruenceLevel : ∀ s, ReferenceDatum.CM.CongruenceLevelInput E s) (h_ReferenceFamily : Moduli.CM.ReferenceFamilyInput) (h_IntegralModel : ArithmeticModels.CM.IntegralModelInput)
    (hNeighborCounting : Neighbor.Counting.CM.NeighborCountingInput)
    (hFrobeniusKernel : Isogenies.NeighborCounting.Prerequisites.FullFrobeniusKernelInput)
    (hCMPoints : AbelianScheme.FrobeniusKernel.CMPoints.Construction.CMPointsInput.{u, v})
    (hCartierDuality : AbelianScheme.FrobeniusKernel.CartierDuality.Construction.FullCartierDualityInput.{0})
    (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput.{0})
    {I : Type u} [Fintype I] (fields : I → Type v)
    [∀ i, Field (fields i)] [∀ i, NumberField (fields i)]
    (excluded : Finset ℕ) (bound : ℕ) :
    ∃ (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)
      (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
      (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count),
      P.IsAdmissible ∧ ∃ hb : P.b = B.b, P.μ = E.val.toRingHom ∧ P.distinguished.val = 0 ∧
      let Kaux := Source.ProjectiveLevel.CM.level E L P hb
        (Theta.Weil.CM.finiteWeilInput φ)

        ∃ R : ℕ, 3 ≤ R ∧ Nbase ∣ R ∧
          PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P R ∧
          P.adelicPrincipalLevel R ≤ Kaux.toSubgroup ∧
          ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P (RingHom.id E) R,
            S.IsFine ∧ S.HasProjectiveBallComponents E.val.toRingHom ∧
            ArithmeticModels.CM.IntegralConclusion P (RingHom.id E) E.val.toRingHom R S ∧
            Source.PreparedReduction.CM.Conclusion E L hTorsionQuotient P (RingHom.id E)
              E.val.toRingHom R S (Theta.Weil.CM.finiteWeilInput φ) fields excluded bound ∧
            ∃ (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : S.ComplexComponent E.val.toRingHom)
              (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice),
              S.IsProjectiveComponent E.val.toRingHom C Y ∧
              let Bref := CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2
              ∃ (ρ : Bref.Domain → Y.analyticSpace)
                (formY : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
                (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1)),
                Bref.IsBallCover R Y ρ ∧ GeometricSource.CM.RepresentsTheta E L φ Y ρ formY ∧
                ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
                  (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 formY.val) ∧
                ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧ ∀ N, 0 < N → N₀ ∣ N →
                  ∃ (π : B.Domain → (X N).analyticSpace)
                    (f : C((X N).analyticSpace, Y.analyticSpace)),
                    B.IsBallCover N (X N) π ∧
                    ContMDiff 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f ∧
                    Function.Surjective f ∧ (∀ z, f (π z) = ρ z) ∧
                    (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ θY = Θ N := by
  obtain ⟨B, places, L, φ, P, hP, hb, hμ, hzero, hlevels⟩ :=
    ZeroMatchedReference.CM.source_family_has_zero_reference
      E d Nbase hNbase X H Θ hsource h_CongruenceLevel h_ReferenceFamily h_IntegralModel
  let Kaux : OpenSubgroup P.FiniteSpecialUnitary :=
    Source.ProjectiveLevel.CM.level E L P hb (Theta.Weil.CM.finiteWeilInput φ)
  obtain ⟨R, hR, hbase, hdeep, haux, S, hS, hball, hintegral, htheta⟩ := hlevels Kaux
  exact ⟨B, places, L, φ, P, hP, hb, hμ, hzero, R, hR, hbase, hdeep, haux,
    S, hS, hball, hintegral,
    ProjectivePreparedReduction.CM.from_inputs E L h_IntegralModel hNeighborCounting hFrobeniusKernel hCMPoints hCartierDuality hTorsionQuotient
      P (RingHom.id E) E.val.toRingHom R S hP ((RingHom.comp_id _).trans hμ.symm) hdeep hS hball
      (Theta.Weil.CM.finiteWeilInput φ) fields excluded bound,
    htheta⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ProjectiveOrdinaryReference.CM.OrdinaryReference
