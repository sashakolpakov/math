import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions

/-! # Matched Level Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedLevelExtraction.CM.Construction

noncomputable section

/-!
# HeckeCycles: checked interface to the supplied CMExtraction specification

This file proves the conversion from CMExtraction's id-vector span to HeckeCycles's
span of images of the entire id-line. It also proves the implication at
a matched level, with the full CMExtraction statement as a named hypothesis.
The imported statement theorem is never used as a proof.

These lemmas are the algebraic endpoint of HeckeCycles. Its original source
predicate has now been replaced by the concrete construction in
`Geometry`, which proves original holomorphic type from actual forms
and Hodge compatibility of actual algebraic restrictions. Construction
of the Hecke eigenspace data is separate from the endpoint lemmas here;
no geometric-to-extraction implication is assumed in a family field.

The definitions below copy CMExtraction's proposition exactly; its proof stub
is not invoked. The CMExtraction specification remains unchanged.
-/

open scoped TensorProduct Classical
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions.CM

universe uV uI uPhi uB

/-- The subspace appearing literally in HeckeCycles's conclusion. -/
def lineImageSpan
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) :
    Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification V) :=
  Submodule.span ℂ
    {z | ∃ f : E →ₗ[ℚ] V,
      ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H f ∧
      ∃ u : ComplexMultiplication.WeightOne.CM.Complexification E,
        u ∈ (ℂ ∙ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)) ∧
        f.baseChange ℂ u = z}

/-- Taking images of a generating vector or its whole line gives the same span. -/
theorem lineImageSpan_eq_cmIdSpan
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V) :
    lineImageSpan E v H = CMExtraction.Definitions.CM.cmIdSpan E v H := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨f, hf, u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [map_smul]
    exact (CMExtraction.Definitions.CM.cmIdSpan E v H).smul_mem a (Submodule.subset_span ⟨f, hf, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro z ⟨f, hf, rfl⟩
    apply Submodule.subset_span
    exact ⟨f, hf, ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1),
      Submodule.mem_span_singleton_self _, rfl⟩

/-- The entire supplied CMExtraction proposition, available only as an explicit input. -/
def CMExtractionInput : Prop :=
  ∀
    (E K : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    [NumberField K] [IsGalois ℚ K]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hv : v.val 1 = true)

    -- K contains the embedding values and active projector coefficients.
    (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K)
    (res : Gal(K/ℚ) → Gal(E/ℚ))
    (_hres : ∀ σ,
      ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) =
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (res σ))

    -- Ambient rational Betti cohomology and its Hodge structure.
    (V : Type uV) [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)

    -- I indexes active projective parameters occurring in theta classes.
    (I : Type uI) (Φ : Type uPhi) [Fintype I]
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification V)
    (P : I → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (A : I → Submodule K (K ⊗[ℚ] V))
    (_hprojector : ∀ i, (P i).comp (P i) = P i)
    (_hcoeff : ∀ i,
      LinearMap.range (P i) = CMExtraction.Definitions.CM.conjugateSpace K (A i) 1)
    (_hHodge : ∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (_htheta : ∀ φ, theta φ ∈ H.holomorphic)
    (_hoccurs : ∀ i, ∃ φ, P i (theta φ) ≠ 0)
    (_hdecompose : ∀ φ, ∑ i, P i (theta φ) = theta φ)

    -- The two possible orientations supplied by the slope calculation.
    (s : I → ℚ)
    (_hextreme : ∀ i, s i = -3 / 2 ∨ s i = 3 / 2)
    -- ExtremeSlopes and equation (6), before calibrating the orientation.
    (_hL421 : ∀ i σ,
      let slope : ℚ :=
        1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (res σ)) : ℚ) * s i / 3
      (slope = 1 →
        CMExtraction.Definitions.CM.conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (slope = 0 →
        CMExtraction.Definitions.CM.conjugateSpace K (A i) σ ≤ H.antiholomorphic))

    -- Restriction from ambient cohomology to the chosen component.
    (B : Type uB) [AddCommGroup B] [Module ℚ B]
    (HB : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure B)
    (restrict : V →ₗ[ℚ] B)
    (_hrestrict : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HB restrict),

    -- Original holomorphy fixes slope 1 and hence the orientation.
    (∀ i, s i = -3 / 2) ∧

    -- Every scalar-conjugate active space has the prescribed Hodge type.
    (∀ i σ,
      (v.val (res σ) = true →
        CMExtraction.Definitions.CM.conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (v.val (res σ) = false →
        CMExtraction.Definitions.CM.conjugateSpace K (A i) σ ≤ H.antiholomorphic)) ∧

    -- Algebraic Betti vectors admit maps supported on the id-line;
    -- these maps lie in the scalar span of rational Hodge maps.
    (∀ i (x : K ⊗[ℚ] V), x ∈ A i →
      ∃ f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V,
        f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H ∧
        ∀ τ : Gal(E/ℚ),
          f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) =
            if τ = 1 then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V x else 0) ∧

    -- Algebraic vectors span the entire complex active eigenspace.
    (∀ i, LinearMap.range (P i) ≤ CMExtraction.Definitions.CM.cmIdSpan E v H) ∧

    -- CM extraction persists after restricting the theta classes.
    (∀ φ, restrict.baseChange ℂ (theta φ) ∈ CMExtraction.Definitions.CM.cmIdSpan E v HB)

/-- With actual matching CMExtraction data at a level, its named prerequisite
implies precisely HeckeCycles's span assertion for each restricted theta class.
This theorem does not assert the missing geometric realization bridge. -/
theorem extraction_at_matched_level
    (E K : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    [NumberField K] [IsGalois ℚ K]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true)

    -- K contains the embedding values and active projector coefficients.
    (hK : ∀ τ : E →ₐ[ℚ] ℂ, τ.fieldRange ≤ K)
    (res : Gal(K/ℚ) → Gal(E/ℚ))
    (hres : ∀ σ,
      ComplexMultiplication.EmbeddingCoefficientField.CM.galoisCoefficientEmbedding K E hK σ
          (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) =
        ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E (res σ))

    -- Ambient rational Betti cohomology and its Hodge structure.
    (V : Type uV) [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)

    -- I indexes active projective parameters occurring in theta classes.
    (I : Type uI) (Φ : Type uPhi) [Fintype I]
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification V)
    (P : I → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (A : I → Submodule K (K ⊗[ℚ] V))
    (hprojector : ∀ i, (P i).comp (P i) = P i)
    (hcoeff : ∀ i,
      LinearMap.range (P i) = CMExtraction.Definitions.CM.conjugateSpace K (A i) 1)
    (hHodge : ∀ i, P i ∈ ComplexMultiplication.Hodge.MapDescent.CM.hodgeHomSubspace H H)
    (htheta : ∀ φ, theta φ ∈ H.holomorphic)
    (hoccurs : ∀ i, ∃ φ, P i (theta φ) ≠ 0)
    (hdecompose : ∀ φ, ∑ i, P i (theta φ) = theta φ)

    -- The two possible orientations supplied by the slope calculation.
    (s : I → ℚ)
    (hextreme : ∀ i, s i = -3 / 2 ∨ s i = 3 / 2)
    -- ExtremeSlopes and equation (6), before calibrating the orientation.
    (hExtremeSlopes : ∀ i σ,
      let slope : ℚ :=
        1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (res σ)) : ℚ) * s i / 3
      (slope = 1 →
        CMExtraction.Definitions.CM.conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (slope = 0 →
        CMExtraction.Definitions.CM.conjugateSpace K (A i) σ ≤ H.antiholomorphic))

    -- Restriction from ambient cohomology to the chosen component.
    (B : Type uB) [AddCommGroup B] [Module ℚ B]
    (HB : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure B)
    (restrict : V →ₗ[ℚ] B)
    (hrestrict : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HB restrict)
    (h_CMExtraction : CMExtractionInput.{uV, uI, uPhi, uB}) :
    ∀ φ, restrict.baseChange ℂ (theta φ) ∈ lineImageSpan E v HB := by
  have h := h_CMExtraction E K v hv hK res hres V H I Φ theta P A
    hprojector hcoeff hHodge htheta hoccurs hdecompose s hextreme hExtremeSlopes
    B HB restrict hrestrict
  intro φ
  rw [lineImageSpan_eq_cmIdSpan]
  exact h.2.2.2.2 φ

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedLevelExtraction.CM.Construction
