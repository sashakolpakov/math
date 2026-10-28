import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceTheta
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DeepSource
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Theta.ThetaRestriction

/-! # Matched Source -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedSource.CM

noncomputable section

/-! Construct one actual reference theta class and all its matching
restrictions from the full source family and the named CongruenceLevel--IntegralModel inputs. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceTheta.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E]
  [NumberField.IsCMField E]

omit [IsGalois ℚ E] in
theorem deep_matched_restrictions
    (B : GeometricSource.CM.BallDatum E) (Λ : Submodule ℤ (GeometricSource.CM.Vec E))
    (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    {places : GeometricSource.CM.Places E} {d : Gal(E/ℚ) → Bool}
    (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (R : ℕ) (hR : 0 < R)
    (ρ : (CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2).Domain → Y.analyticSpace)
    (hρ : (CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2).IsBallCover R Y ρ)
    (formY : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0)
    (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hformY : GeometricSource.CM.RepresentsTheta E L φ Y ρ formY)
    (hθY : ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace Y.toOver) 1 θY =
      (Y.deRhamBettiIso 1).hom (Y.deRhamClass 1 formY.val))
    (Nbase : ℕ) (hNbase : 0 < Nbase) (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hlevels : ∀ N, 0 < N → Nbase ∣ N →
      ∃ π : B.Domain → (X N).analyticSpace, B.IsBallCover N (X N) π ∧
        ∃ form : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms (X N).analyticModel (X N).analyticSpace 1 0,
          GeometricSource.CM.RepresentsTheta E L φ (X N) π form ∧
          ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1 (Θ N) =
            ((X N).deRhamBettiIso 1).hom ((X N).deRhamClass 1 form.val)) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧ ∀ N, 0 < N → N₀ ∣ N →
      ∃ (π : B.Domain → (X N).analyticSpace) (f : C((X N).analyticSpace, Y.analyticSpace)),
        B.IsBallCover N (X N) π ∧
        ContMDiff 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f ∧
        Function.Surjective f ∧ (∀ z, f (π z) = ρ z) ∧
        (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ θY = Θ N := by
  let Bref := CoverFactor.CM.withLattice E B Λ hΛ.1 hΛ.2.1 hΛ.2.2
  obtain ⟨N₀, hN₀, hbase, hcontain⟩ :=
    ReferenceDatum.CM.source_levels_refine_reference E B Λ hΛ R Nbase hR hNbase
  refine ⟨N₀, hN₀, hbase, ?_⟩
  intro N hN hdiv
  let : FiniteDimensional ℚ ((X N).rationalCohomology 1) := (H N).finiteDimensional
  obtain ⟨π, hπ, form, hform, hθ⟩ := hlevels N hN (hbase.trans hdiv)
  have hsub : ∀ g, B.principalLevel N g → Bref.principalLevel R g :=
    fun g hg => (ReferenceDatum.CM.principalLevel_iff E Bref R g).mpr (hcontain N hdiv g hg)
  obtain ⟨f, hf, hsurj, hcomp⟩ := CoverFactor.CM.map_of_principal_containment E B Λ
    hΛ.1 hΛ.2.1 hΛ.2.2 R N (X N) Y π ρ hπ hρ hsub
  have hhol := CoverDerivative.CM.descended_map_mdifferentiable π ρ hπ.2.1
    hπ.2.2.1 hπ.2.2.2.1 hπ.2.2.2.2.1 hρ.2.2.2.1 f hcomp
  have hsmooth := (CoverSmooth.CM.quotient_map_contMDiff B N (X N) Y π hπ f hhol).1
  let fc : C((X N).analyticSpace, Y.analyticSpace) := ⟨f, hf⟩
  exact ⟨π, fc, hπ, hsmooth, hsurj, hcomp,
    Theta.ThetaRestriction.CM.theta_class_restricts E L φ (X N) Y N π hπ ρ fc hsmooth hcomp
      form formY hform hformY (Θ N) θY hθ hθY⟩

/-- The reference class and every matching restriction are conclusions
of the actual source geometry. No reference theta class is assumed. -/
theorem source_family_has_matched_reference
    (d : Gal(E/ℚ) → Bool) (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ)
    (h_CongruenceLevel : ∀ s, ReferenceDatum.CM.CongruenceLevelInput E s) (h_ReferenceFamily : Moduli.CM.ReferenceFamilyInput) (h_IntegralModel : ArithmeticModels.CM.IntegralModelInput) :
    ∃ (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)
      (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
      (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count),
      P.IsAdmissible ∧ P.b = B.b ∧ P.μ = E.val.toRingHom ∧
      ∀ Kaux : OpenSubgroup P.FiniteSpecialUnitary,
        ∃ R : ℕ, 3 ≤ R ∧ Nbase ∣ R ∧
          PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P R ∧
          P.adelicPrincipalLevel R ≤ Kaux.toSubgroup ∧
          ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P (RingHom.id E) R,
            S.IsFine ∧ S.HasProjectiveBallComponents E.val.toRingHom ∧
            ArithmeticModels.CM.IntegralConclusion P (RingHom.id E) E.val.toRingHom R S ∧
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
  obtain ⟨B, places, L, φ, hlevels⟩ := hsource
  obtain ⟨P, hP, hb, hemb, hdist, _hsign⟩ :=
    PELDatum.CM.admissible_reference_datum E B places (h_CongruenceLevel places.count)
      (fun i => d (places.representative i))
  have hμ : P.μ = E.val.toRingHom := by
    unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ
    rw [hemb, hdist, ReferenceDatum.CM.embeddings_distinguished]
  have hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hΛ, _⟩ := hP
    exact hΛ
  let Bref := CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2
  obtain ⟨M, hM, hMbase, hcontain⟩ := ReferenceTheta.CM.reference_level_bound E B P.lattice hΛ Nbase hNbase
  refine ⟨B, places, L, φ, P, hP, hb, hμ, ?_⟩
  intro Kaux
  obtain ⟨R, hR, hMR, hmodels⟩ := ArithmeticModels.CM.deep_integral_models places.count
    (ReferenceDatum.CM.source_degree E places).1 (ReferenceDatum.CM.source_degree E places).2 P hP
    (RingHom.id E) E.val.toRingHom (by rw [RingHom.comp_id, hμ])
    h_ReferenceFamily h_IntegralModel Kaux M hM
  have hRpos : 0 < R := lt_of_lt_of_le (by decide : 0 < 3) hR
  obtain ⟨hadelic, hdeep, S, hS, hball, ⟨Γ, C, Y, hΓ, hY, href⟩, hintegral⟩ :=
    hmodels R hRpos (dvd_refl R)
  obtain ⟨ρ, hρ⟩ := ReferenceCover.CM.reference_cover_as_source E Bref P hb hμ rfl R Y hY.1 Γ hΓ href
  obtain ⟨π, hπ, form, hform, hθ⟩ := hlevels Nbase hNbase (dvd_refl Nbase)
  obtain ⟨f, _hf, _hsurj, _hcomp, formY, hformY, hθY⟩ := ReferenceTheta.CM.reference_theta_from_source E
    (hΛ := hΛ) L φ (X Nbase) Y Nbase R π ρ hπ hρ (hcontain R hMR) form hform (Θ Nbase) hθ
  let θY := (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ (Θ Nbase)
  refine ⟨R, hR, hMbase.trans hMR, hdeep, hadelic, S, hS, hball, hintegral,
    Y, C, hΛ, hY, ρ, formY, θY, hρ, hformY, hθY, ?_⟩
  exact deep_matched_restrictions E B P.lattice hΛ L φ Y R hRpos ρ hρ
    formY θY hformY hθY Nbase hNbase X H Θ hlevels

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedSource.CM
