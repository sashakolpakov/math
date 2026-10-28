import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Definitions
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarTrace

/-! # Galois Signs -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisSigns.CM

noncomputable section

/-! The CMExtraction statement, with its proof supplied by the completed development. -/

open scoped TensorProduct Classical

/-- CMExtraction: holomorphic theta classes calibrate the conjugate signs,
and their active eigenspaces admit CM extraction by rational Hodge maps. -/
theorem cm_extraction_from_galois_conjugate_hodge_signs
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
    (V : Type*) [AddCommGroup V] [Module ℚ V]
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure V)

    -- I indexes active projective parameters occurring in theta classes.
    (I Φ : Type*) [Fintype I]
    (theta : Φ → ComplexMultiplication.WeightOne.CM.Complexification V)
    (P : I → Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification V))
    (A : I → Submodule K (K ⊗[ℚ] V))
    (hprojector : ∀ i, (P i).comp (P i) = P i)
    (hcoeff : ∀ i,
      LinearMap.range (P i) = Definitions.CM.conjugateSpace K (A i) 1)
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
        Definitions.CM.conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (slope = 0 →
        Definitions.CM.conjugateSpace K (A i) σ ≤ H.antiholomorphic))

    -- Restriction from ambient cohomology to the chosen component.
    (B : Type*) [AddCommGroup B] [Module ℚ B]
    (HB : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure B)
    (restrict : V →ₗ[ℚ] B)
    (hrestrict : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HB restrict) :

    -- Original holomorphy fixes slope 1 and hence the orientation.
    (∀ i, s i = -3 / 2) ∧

    -- Every scalar-conjugate active space has the prescribed Hodge type.
    (∀ i σ,
      (v.val (res σ) = true →
        Definitions.CM.conjugateSpace K (A i) σ ≤ H.holomorphic) ∧
      (v.val (res σ) = false →
        Definitions.CM.conjugateSpace K (A i) σ ≤ H.antiholomorphic)) ∧

    -- Algebraic Betti vectors admit maps supported on the id-line;
    -- these maps lie in the scalar span of rational Hodge maps.
    (∀ i (x : K ⊗[ℚ] V), x ∈ A i →
      ∃ f : ComplexMultiplication.WeightOne.CM.Complexification E →ₗ[ℂ] ComplexMultiplication.WeightOne.CM.Complexification V,
        f ∈ ComplexMultiplication.Hodge.MapDescent.CM.rationalHodgeMapSpan (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) H ∧
        ∀ τ : Gal(E/ℚ),
          f (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)) =
            if τ = 1 then ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V x else 0) ∧

    -- Algebraic vectors span the entire complex active eigenspace.
    (∀ i, LinearMap.range (P i) ≤ Definitions.CM.cmIdSpan E v H) ∧

    -- CM extraction persists after restricting the theta classes.
    (∀ φ, restrict.baseChange ℂ (theta φ) ∈ Definitions.CM.cmIdSpan E v HB) := by
  exact SameTestProjector.cm_extraction_from_galois_conjugate_hodge_signs
    E K v hv hK res hres V H
    (ScalarTrace.scalarTraceInput_of_numberField K (E →ₗ[ℚ] V))
    I Φ theta P A hprojector hcoeff hHodge htheta hoccurs hdecompose s hextreme hExtremeSlopes
    B HB restrict hrestrict

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisSigns.CM
