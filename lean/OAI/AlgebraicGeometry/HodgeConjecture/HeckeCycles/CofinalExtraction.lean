import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpanRestriction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Naturality

/-! # Cofinal Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CofinalExtraction.CM

noncomputable section

/-! Carry extraction on the actual reference theta class to all the
constructed deeper source levels, using their actual holomorphic maps. -/

open scoped Classical _root_.Manifold ContDiff TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AnalyticPullback.CM

theorem extraction
    (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hHodgeDecomposition : CMExtraction.Mem.HodgeDecompositionInput)
    (Nbase N₀ : ℕ) (hN₀ : 0 < N₀) (hbase : Nbase ∣ N₀)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : ∀ N, (H N).holomorphic = ((X N).pureBettiSubspace 1 0).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1))
    (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (θY : ComplexMultiplication.WeightOne.CM.Complexification (Y.rationalCohomology 1))
    (hextract : θY ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v
      (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation))
    (hmaps : ∀ N, 0 < N → N₀ ∣ N → ∃ f : C((X N).analyticSpace, Y.analyticSpace),
      ContMDiff 𝓘(ℂ, (X N).analyticModel) 𝓘(ℂ, Y.analyticModel) ∞ f ∧
      (AnalyticPullback.CM.pullbackQ f 1).hom.baseChange ℂ θY = Θ N) :
    ∃ M : ℕ, 0 < M ∧ Nbase ∣ M ∧
      ∀ N, 0 < N → M ∣ N → Θ N ∈ MatchedLevelExtraction.CM.Construction.lineImageSpan E v (H N) := by
  refine ⟨N₀, hN₀, hbase, ?_⟩
  intro N hN hdiv
  obtain ⟨f, hf, hθ⟩ := hmaps N hN hdiv
  have hmap := AnalyticPullback.CM.pullback_isHodgeMap f hf (H N)
    (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation) (hH N)
    (CMExtraction.Naturality.canonicalH1_integral_holomorphic hHodgeDecomposition Y)
  have h := SpanRestriction.CM.lineImageSpan_pullback E v
    (CMExtraction.Mem.canonicalH1 hHodgeDecomposition Y.presentation) (H N)
    (AnalyticPullback.CM.pullbackQ f 1).hom hmap hextract
  exact hθ ▸ h

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CofinalExtraction.CM
