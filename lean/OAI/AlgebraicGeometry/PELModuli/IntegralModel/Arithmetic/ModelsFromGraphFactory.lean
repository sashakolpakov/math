import OAI.AlgebraicGeometry.PELModuli.IntegralModel.ModelsFromPureFactory
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.UniformStableGraphClassification
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Alternative

/-! # Models From Graph Factory -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ModelsFromGraphFactory

noncomputable section

/-! The checked stable-Hilbert construction at sufficiently large prime
levels supplies the exact arithmetic models used by IntegralModel. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem arithmeticPrimePELModels_of_graph_factory
    {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible) (hs : 0 < s)
    (hFactory : ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
      (p : ℕ) [NeZero p], 3 ≤ p → IsUnit (p : R) → IsUnit (2 : R) →
      IsUnit (∏ i, (P.polarizationType i : R)) →
      ∀ d : ℕ, 0 < d → IsUnit (d : R) →
        AbelianModuli.HilbertConstruction.GraphPower.LocusPresentation.GraphPowerLocusFactory R (3 * s) p d P.polarizationType) :
    PrimeModels.ArithmeticPrimePELModels P := by
  have hδ : ∀ i, 0 < P.polarizationType i := by
    rcases hP with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
    exact hpos
  let g := 3 * s
  let δ := P.polarizationType
  let d := AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree g δ
  let D := AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters.uniformRelationDegree g δ
  let B := max (AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * AbelianModuli.HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ)
    (AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D)
  have hd : 0 < d := AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingDegree_pos g δ hδ
  have hH := AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters.uniformAuxiliaryParameters_rankProfile P hP hs
  have hD := AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters.uniformHilbertFamilyDegree_le_relationDegree g δ
  refine ModelsFromPureFactory.arithmeticPrimePELModels_of_pure_models P B d hd ?_
    Alternative.AlternativeStrategies.provedEndomorphismEquationsInput
  intro p _ hp3 hpB R _ _ hpR h2R hdR hδR
  let Ψ := hFactory R p hp3 hpR h2R hδR
  let Φ := Ψ d hd hdR
  let M := UniformStableGraph.ReferenceFamily.uniformStableGraphModel R g δ hδ p hp3 D hH hD Φ
  let Q := UniformStableGraph.ReferenceFamily.uniformStableGraphModel_quasiProjective R g δ hδ p hp3 D hH hD Φ
  have hp2 : p ≤ p ^ 2 := by simpa only [pow_two] using Nat.le_mul_self p
  have hframe : AbelianModuli.HilbertConstruction.Graph.EmbeddingNumerics.graphUniformEmbeddingSectionRank g δ * AbelianModuli.HilbertConstruction.Uniform.GraphIntersectionData.graphTorsionHyperplaneDegree g δ < p ^ 2 :=
    ((Nat.le_max_left _ _).trans_lt hpB).trans_le hp2
  have hlarge : AbelianModuli.HilbertConstruction.Bounded.GraphTorsionSectionDetection.boundedGraphTorsionDegree g δ D < p ^ 2 :=
    ((Nat.le_max_right _ _).trans_lt hpB).trans_le hp2
  exact ⟨M, ⟨Q⟩, UniformStableGraphClassification.ReferenceFamily.uniformStableGraphModel_isFine R g δ hδ p hp3 D hH hD Φ hpR
    (Nat.mul_pos (by decide) hs) (AbelianModuli.ReferenceFamily.UniformAuxiliaryParameters.uniformRelationDegree_pos g δ) hframe hlarge Ψ⟩

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Arithmetic.ModelsFromGraphFactory
