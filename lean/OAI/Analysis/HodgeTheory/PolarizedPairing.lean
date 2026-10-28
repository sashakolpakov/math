import OAI.AlgebraicGeometry.ComplexMultiplication.CM.Polarization
import OAI.AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType
import OAI.Analysis.HodgeTheory.TopForms

/-! # Polarized Pairing -/

namespace OAI.Analysis.HodgeTheory.PolarizedPairing.Constructions

noncomputable section

/-! PolarizedPairing: positivity and nonvanishing of polarized pairings.
This file does not import the statement specification or any statement stub.
The top-form pairing is constructed by complex-coordinate wedge coefficients
and a finite smooth partition of unity. Conjugation uses the implemented
`CM.HodgeComparisonProof.conjugateSmoothForm`; the statement schema's shorter name did
not exist. The dimension equality is explicit in the new integral API.
-/

open scoped TensorProduct _root_.Manifold ContDiff

theorem rational_pairing_conjugation
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (Q : LinearMap.BilinForm ℚ U) (u v : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) :
    Q.baseChange ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U v) =
      star (Q.baseChange ℂ u v) := by
  induction u using TensorProduct.inductionOn with
  | add u w hu hw => simp only [map_add, LinearMap.add_apply, hu, hw, star_add]
  | tmul a x =>
    induction v using TensorProduct.inductionOn with
    | add v w hv hw => simp only [map_add, hv, hw, star_add]
    | tmul b y => simp

theorem pure_pairing_conjugate_ne_zero
    {U : Type*} [AddCommGroup U] [Module ℚ U]
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (P : AlgebraicGeometry.ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
    (u : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
    (hu : u ∈ H.holomorphic ∨ u ∈ H.antiholomorphic) (hu0 : u ≠ 0) :
    P.form.baseChange ℂ u (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) ≠ 0 := by
  have holo (w : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U) (hw : w ∈ H.holomorphic) (hw0 : w ≠ 0) :
      P.form.baseChange ℂ w (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U w) ≠ 0 := by
    intro hz
    have hp := P.hodge_positive w hw hw0
    simp [hz] at hp
  rcases hu with hh | ha
  · exact holo u hh hu0
  · have hc : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u ∈ H.holomorphic :=
      (H.conjugate_mem _).mp (by simpa using ha)
    have hc0 : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u ≠ 0 := by
      intro hz
      apply hu0
      have h := congrArg (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U) hz
      simpa using h
    have hn := holo (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u) hc hc0
    rw [rational_pairing_conjugation] at hn
    intro hz
    exact hn (by simp [hz])

/-- Polarization pairs nonzero vectors on opposite embedding lines
nontrivially. Rank one and Hodge compatibility give purity of each line. -/
theorem opposite_embedding_pairing_ne_zero
    {E U : Type*}
    [Field E] [NumberField E] [Algebra ℚ E]
    [AddCommGroup U] [Module ℚ U] [Module E U]
    [IsScalarTower ℚ E U]
    (H : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)
    (P : AlgebraicGeometry.ComplexMultiplication.CM.Polarization.WeightOnePolarization H)
    (hCM : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.RankOneCMAction E H)
    (σ : E →ₐ[ℚ] ℂ)
    (u v : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification U)
    (hu : u ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ)
    (hv : v ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ))
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) :
    P.form.baseChange ℂ u v ≠ 0 := by
  have hpure : u ∈ H.holomorphic ∨ u ∈ H.antiholomorphic :=
    (hCM.embeddingSpace_hodge_dichotomy σ).imp (fun h => h hu) (fun h => h hu)
  have hpair := pure_pairing_conjugate_ne_zero H P u hpure hu0
  have hc : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u ∈ AlgebraicGeometry.ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ) :=
    AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_mem_embeddingSpace E U σ hu
  have hc0 : AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.coefficientConjugation U u ≠ 0 := by
    intro hz
    exact hpair (by rw [hz]; simp)
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one
    (hCM.embeddingSpace_finrank (AlgebraicGeometry.ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ)) hc hc0
  rw [hspan] at hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  have hc : c ≠ 0 := by
    intro hz
    exact hv0 (by simp [hz])
  simpa using mul_ne_zero hc hpair

/-- A nonzero holomorphic top form has strictly positive phase-normalized
integral pairing with its conjugate. No Kähler hypothesis is needed. -/
theorem holomorphic_top_form_pairing_positive
    {n : ℕ}
    {E : Type*}
    [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E]
    [IsScalarTower ℝ ℂ E] [FiniteDimensional ℂ E]
    {M : Type*}
    [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ∞ M]
    [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (hdim : Module.finrank ℂ E = n)
    (form : DifferentialForms.Manifold.Algebra.SmoothManifoldForm E M (n + 0))
    (htype : DifferentialForms.Manifold.ManifoldBidegree.HasManifoldBidegree E M n 0 form.val)
    (_hclosed : DifferentialForms.Manifold.Algebra.SmoothManifoldForm.d form = 0)
    (hne : form ≠ 0) :
    let z := TopForms.Constructions.PolarizedPairing.complexOrientedTopPairing hdim form
      (AlgebraicGeometry.ComplexMultiplication.HodgeComparison.Conjugation.CM.Construction.conjugateSmoothForm form)
    (Complex.I ^ (n * n) * z).im = 0 ∧
    0 < (Complex.I ^ (n * n) * z).re ∧
    z ≠ 0 := by
  let : FiniteDimensional ℝ E := FiniteDimensional.trans ℝ ℂ E
  exact TopForms.Constructions.PolarizedPairing.topPairingWith_positive (Integration.Constructions.PolarizedPairing.canonicalChartPartition E M)
    ((Module.finBasis ℂ E).reindex (finCongr hdim)) form htype hne

end

end OAI.Analysis.HodgeTheory.PolarizedPairing.Constructions
