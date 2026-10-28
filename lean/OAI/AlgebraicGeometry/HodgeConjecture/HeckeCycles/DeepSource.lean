import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverSmooth
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels

/-! # Deep Source -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DeepSource.CM

noncomputable section

/-! Assemble deep reference models and actual maps from the given source
quotients. Every cover on the source side comes from the original theta
family; the target cover comes from ReferenceFamily and the integral model from IntegralModel. -/

open scoped Classical _root_.Manifold ContDiff
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceCover.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CoverFactor.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticModels.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Moduli.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PELDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E]
  [IsGalois ℚ E] [NumberField.IsCMField E]

omit [IsGalois ℚ E] in
/-- A fixed reference component is dominated by all sufficiently divisible
source levels. The actual reference covering is retained in the result. -/
theorem deep_maps_to_reference
    (B : GeometricSource.CM.BallDatum E) {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice)
    (hb : P.b = B.b) (hμ : P.μ = E.val.toRingHom)
    (R : ℕ) (hR : 0 < R) (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (hdim : Y.complexDimension = 2)
    (Γ : Subgroup (GeometricSource.CM.Vec E ≃ₗ[E] GeometricSource.CM.Vec E))
    (hΓ : ∀ g, g ∈ Γ ↔
      (NumberTheory.ArithmeticGroups.Data.CongruenceLevel.PrincipalLevel P.b P.lattice R g ∧
        LinearMap.det g.toLinearMap = 1))
    (href : P.IsUniformizedBy Y Γ)
    (Nbase : ℕ) (hNbase : 0 < Nbase) (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (hsource : ∀ N, 0 < N → Nbase ∣ N →
      ∃ π : B.Domain → (X N).analyticSpace, B.IsBallCover N (X N) π) :
    let Bref := CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2
    ∃ ρ : Bref.Domain → Y.analyticSpace, Bref.IsBallCover R Y ρ ∧
      ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
        ∀ N, 0 < N → N₀ ∣ N →
          ∃ (π : B.Domain → (X N).analyticSpace)
            (f : (X N).analyticSpace → Y.analyticSpace),
            B.IsBallCover N (X N) π ∧ Continuous f ∧
              MDifferentiable 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) f ∧
              ContMDiff 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f ∧
              ContMDiff 𝓘(ℝ, (X N).analyticModel) 𝓘(ℝ, Y.analyticModel) ∞ f ∧
              Function.Surjective f ∧
              ∀ z : B.Domain, f (π z) = ρ z := by
  let Bref := CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2
  obtain ⟨ρ, hρ⟩ := ReferenceCover.CM.reference_cover_as_source E Bref P hb hμ rfl R Y hdim Γ hΓ href
  obtain ⟨N₀, hN₀, hbase, hlevels⟩ :=
    ReferenceDatum.CM.source_levels_refine_reference E B P.lattice hΛ R Nbase hR hNbase
  refine ⟨ρ, hρ, N₀, hN₀, hbase, ?_⟩
  intro N hN hdiv
  obtain ⟨π, hπ⟩ := hsource N hN (hbase.trans hdiv)
  have hcontain : ∀ g, B.principalLevel N g → Bref.principalLevel R g := by
    intro g hg
    exact (ReferenceDatum.CM.principalLevel_iff E Bref R g).mpr (hlevels N hdiv g hg)
  obtain ⟨f, hf, hsurj, hcomp⟩ := CoverFactor.CM.map_of_principal_containment E B P.lattice
    hΛ.1 hΛ.2.1 hΛ.2.2 R N (X N) Y π ρ hπ hρ hcontain
  have hhol := CoverDerivative.CM.descended_map_mdifferentiable π ρ hπ.2.1
    hπ.2.2.1 hπ.2.2.2.1 hπ.2.2.2.2.1 hρ.2.2.2.1 f hcomp
  have hsmooth := CoverSmooth.CM.quotient_map_contMDiff B N (X N) Y π hπ f hhol
  exact ⟨π, f, hπ, hf, hhol, hsmooth.1, hsmooth.2, hsurj, hcomp⟩

/-- Starting with the actual source family, choose a reference PEL datum,
then obtain a deep integral model and its principal ball component. All
sufficiently deep original quotients map to that same component. -/
theorem source_family_has_deep_reference
    (d : Gal(E/ℚ) → Bool) (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ)
    (h_CongruenceLevel : ∀ s, ReferenceDatum.CM.CongruenceLevelInput E s) (h_ReferenceFamily : Moduli.CM.ReferenceFamilyInput) (h_IntegralModel : ArithmeticModels.CM.IntegralModelInput) :
    ∃ (B : GeometricSource.CM.BallDatum E) (places : GeometricSource.CM.Places E)
      (L : GeometricSource.CM.LinePeriod E B places d) (φ : GeometricSource.CM.FiniteInput (GeometricSource.CM.Positions E places))
      (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E places.count),
      P.IsAdmissible ∧ P.b = B.b ∧ P.μ = E.val.toRingHom ∧
      (∀ N, 0 < N → Nbase ∣ N →
        ∃ π : B.Domain → (X N).analyticSpace,
          B.IsBallCover N (X N) π ∧
          ∃ form : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms
            (X N).analyticModel (X N).analyticSpace 1 0,
            GeometricSource.CM.RepresentsTheta E L φ (X N) π form ∧
            ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1 (Θ N) =
              ((X N).deRhamBettiIso 1).hom ((X N).deRhamClass 1 form.val)) ∧
      ∀ Kaux : OpenSubgroup P.FiniteSpecialUnitary,
        ∃ (R : ℕ), 3 ≤ R ∧ Nbase ∣ R ∧
          PELModuli.IntegralModel.PEL.Has.IsSufficientlyDeepFullLevel P R ∧
          P.adelicPrincipalLevel R ≤ Kaux.toSubgroup ∧
          ∃ S : AbelianModuli.ReferenceFamily.Models.FinePELModel P (RingHom.id E) R,
            S.IsFine ∧ S.HasProjectiveBallComponents E.val.toRingHom ∧
            ArithmeticModels.CM.IntegralConclusion P (RingHom.id E) E.val.toRingHom R S ∧
            ∃ (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (C : S.ComplexComponent E.val.toRingHom)
              (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice),
              S.IsProjectiveComponent E.val.toRingHom C Y ∧
              let Bref := CoverFactor.CM.withLattice E B P.lattice hΛ.1 hΛ.2.1 hΛ.2.2
              ∃ ρ : Bref.Domain → Y.analyticSpace, Bref.IsBallCover R Y ρ ∧
                ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
                  ∀ N, 0 < N → N₀ ∣ N →
                    ∃ (π : B.Domain → (X N).analyticSpace)
                      (f : (X N).analyticSpace → Y.analyticSpace),
                      B.IsBallCover N (X N) π ∧ Continuous f ∧
                        MDifferentiable 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) f ∧
                        ContMDiff 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f ∧
                        ContMDiff 𝓘(ℝ, (X N).analyticModel) 𝓘(ℝ, Y.analyticModel) ∞ f ∧
                        Function.Surjective f ∧
                        ∀ z : B.Domain, f (π z) = ρ z := by
  obtain ⟨B, places, L, φ, hlevels⟩ := hsource
  obtain ⟨P, hP, hb, hemb, hdist, _hsign⟩ :=
    PELDatum.CM.admissible_reference_datum E B places (h_CongruenceLevel places.count)
      (fun i => d (places.representative i))
  have hμ : P.μ = E.val.toRingHom := by
    unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.μ
    rw [hemb, hdist, ReferenceDatum.CM.embeddings_distinguished]
  refine ⟨B, places, L, φ, P, hP, hb, hμ, hlevels, ?_⟩
  intro Kaux
  obtain ⟨R, hR, hbase, hmodels⟩ := ArithmeticModels.CM.deep_integral_models places.count
    (ReferenceDatum.CM.source_degree E places).1 (ReferenceDatum.CM.source_degree E places).2 P hP
    (RingHom.id E) E.val.toRingHom (by rw [RingHom.comp_id, hμ])
    h_ReferenceFamily h_IntegralModel Kaux Nbase hNbase
  have hRpos : 0 < R := lt_of_lt_of_le (by decide : 0 < 3) hR
  obtain ⟨hadelic, hdeep, S, hS, hball, ⟨Γ, C, Y, hΓ, hY, href⟩, hintegral⟩ :=
    hmodels R hRpos (dvd_refl R)
  have hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice P.lattice := by
    obtain ⟨_, _, _, _, _, _, _, _, _, hΛ, _⟩ := hP
    exact hΛ
  refine ⟨R, hR, hbase, hdeep, hadelic, S, hS, hball, hintegral, Y, C, hΛ, hY, ?_⟩
  exact deep_maps_to_reference E B P hΛ hb hμ R hRpos Y hY.1 Γ hΓ href
    Nbase hNbase X (fun N hN hdiv => by
      obtain ⟨π, hπ, _⟩ := hlevels N hN hdiv
      exact ⟨π, hπ⟩)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.DeepSource.CM
