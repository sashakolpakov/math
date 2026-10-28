import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Albanese
import OAI.AlgebraicGeometry.Albanese.HodgeComparisonIs

/-! # Hecke Cycles -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HeckeCycles.CM

noncomputable section

section

/-! ThetaCycle assembly using the proved native Albanese comparison HodgeComparison.
The full DegreeTwo weight-one and Construction existence propositions remain named inputs.
No statement stub or global ThetaCycle existence theorem is imported or invoked. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj

/-- The full original HodgeComparison input is discharged by its native proof. -/
theorem nativeHodgeComparisonInput : DegreeTwo.Transport.Constructions.HodgeComparisonInput := by
  intro X x₀ A a ha
  exact Albanese.HodgeComparisonIs.CM.Construction.albanese_h1_hodge_iso X x₀ A a ha

/-- Construct an actual surface map using the proved Albanese comparison. -/
theorem surface_hodge_map_algebraic_native
    (hDegreeTwo : Albanese.CM.WeightOneInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput)
    {U : Type} [AddCommGroup U] [Module ℚ U]
    (J : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U) (R : ComplexMultiplication.CMKnownResults.CM.HodgeRealization J)
    (S : Cm.ProjectiveSurface)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (S.variety.rationalCohomology 1))
    (hH : DegreeTwo.Transport.Constructions.IsCanonicalH1 S.variety H)
    (u : U →ₗ[ℚ] S.variety.rationalCohomology 1) (hu : ComplexMultiplication.WeightOne.CM.IsHodgeMap J H u) :
    ∃ n : ℕ, 0 < n ∧
      ∃ f : S.variety.toOver ⟶ R.abelianVariety.toOver,
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 f).hom.comp R.comparison.toLinearMap =
          (n : ℚ) • u := by
  exact Albanese.CM.surface_hodge_map_algebraic hDegreeTwo hConstruction nativeHodgeComparisonInput J R S H hH u hu

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
  (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))

theorem algebraic_maps_of_hodge_term_native
    (hDegreeTwo : Albanese.CM.WeightOneInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput)
    (S : Cm.ProjectiveSurface)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (S.variety.rationalCohomology 1))
    (hH : DegreeTwo.Transport.Constructions.IsCanonicalH1 S.variety H)
    (u : Fin 4 → (K →ₗ[ℚ] S.variety.rationalCohomology 1))
    (hu : ∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)) H (u i))
    (hn : Extraction.CM.fourValue S (fun i => Extraction.CM.hodgeLineImage K S.variety (u i) (Extraction.CM.slotLabel K i)) ≠ 0) :
    ∃ (f : (i : Fin 4) → S.variety.toOver ⟶ (R i).abelianVariety.toOver)
      (n : Fin 4 → ℕ),
      (∀ i, 0 < n i) ∧
      (∀ i, (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (f i)).hom.comp
        (R i).comparison.toLinearMap = (n i : ℚ) • u i) ∧
      (∀ i, Extraction.CM.pulledEmbedding K v R S.variety f i =
        (n i : ℂ) • Extraction.CM.hodgeLineImage K S.variety (u i) (Extraction.CM.slotLabel K i)) ∧
      S.evaluate (Cm.fourClass K v R S.variety f) ≠ 0 := by
  exact Albanese.CM.algebraic_maps_of_hodge_term K v R hDegreeTwo hConstruction nativeHodgeComparisonInput S H hH u hu hn

theorem algebraic_maps_of_wedge_data_native
    (hDegreeTwo : Albanese.CM.WeightOneInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput)
    (S : Cm.ProjectiveSurface)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (S.variety.rationalCohomology 1))
    (hH : DegreeTwo.Transport.Constructions.IsCanonicalH1 S.variety H)
    (Θ : Fin 4 → Submodule ℂ (S.variety.complexCohomology 1))
    (hCM : ∀ i, Θ i ≤ Cm.cmLineSpan K S.variety H (v i) (Extraction.CM.slotLabel K i))
    (ξ ζ : S.variety.complexCohomology 2)
    (hξ : ξ ∈ Cm.wedgeSpan S.variety (Θ 0) (Θ 1))
    (hη : ζ ∈ Cm.wedgeSpan S.variety (Θ 2) (Θ 3))
    (hn : S.evaluate (Cm.cup S.variety 2 2 ξ ζ) ≠ 0) :
    ∃ f : (i : Fin 4) → S.variety.toOver ⟶ (R i).abelianVariety.toOver,
      S.evaluate (Cm.fourClass K v R S.variety f) ≠ 0 := by
  exact Albanese.CM.algebraic_maps_of_wedge_data K v R hDegreeTwo hConstruction nativeHodgeComparisonInput S H hH Θ hCM ξ ζ hξ hη hn

end

section

/-- Full HeckeCycles, with the native HodgeComparison canonical-H¹ predicate. -/
def HeckeCyclesInput : Prop :=
  ∀
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (_hv : v.val 1 = true)
    (d : Gal(E/ℚ) → Bool)
    (_hd : ∀ τ, d τ = v.val (τ⁻¹))
    (Nbase : ℕ)
    (_hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N : ℕ,
      ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (_hH : ∀ N, Albanese.HodgeComparisonIs.CM.Construction.IsCanonicalH1 (X N) (H N))
    (Θ : ∀ N : ℕ,
      ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (_hsource : HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily E d Nbase X Θ),
    ∃ N₀ : ℕ, 0 < N₀ ∧ Nbase ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N →
        Θ N ∈ Submodule.span ℂ
          {z | ∃ f : E →ₗ[ℚ] (X N).rationalCohomology 1,
            ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure E v) (H N) f ∧
            ∃ u : ComplexMultiplication.WeightOne.CM.Complexification E,
              u ∈ (ℂ ∙ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector E
                (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1)) ∧
              f.baseChange ℂ u = z}

end

section

/-! Exact transport from HeckeCycles's full identity-line image span to the native
Betti CM lines. The conjugate slots use actual singular-cochain conjugation,
which the native HodgeComparison comparison identifies with conjugation of closed forms. -/

open scoped Classical

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

omit [IsGalois ℚ K] [NumberField.IsCMField K] in
theorem coefficient_conjugation_embedding (σ : K →ₐ[ℚ] ℂ) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation K (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K σ) =
      ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ) := by
  apply (ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv K).injective
  ext ρ
  rw [ComplexMultiplication.CM.TypeHodgeStructure.fieldComplexificationEquiv_conjugation,
    ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector, ComplexMultiplication.EmbeddingDecomposition.CM.fieldComplexificationEquiv_embeddingVector]
  have hi : ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding ρ = σ ↔ ρ = ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ := by
    constructor
    · intro h
      rw [← h, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
    · intro h
      rw [h, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding_involutive]
  simp only [Pi.single_apply, hi]
  split_ifs <;> simp

def rawCMLineSpan
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (τ : Gal(K/ℚ)) : Submodule ℂ (ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1)) :=
  Submodule.span ℂ {z | ∃ f : K →ₗ[ℚ] X.rationalCohomology 1,
    ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K v) H f ∧
    ∃ u : ComplexMultiplication.WeightOne.CM.Complexification K,
      u ∈ ℂ ∙ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ) ∧ f.baseChange ℂ u = z}

theorem raw_span_to_betti
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (τ : Gal(K/ℚ)) (θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθ : θ ∈ rawCMLineSpan K X H v τ) :
    ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θ ∈
      Cm.cmLineSpan K X H v τ := by
  have hs : rawCMLineSpan K X H v τ ≤ (Cm.cmLineSpan K X H v τ).comap
      (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1) := by
    apply Submodule.span_le.mpr
    rintro z ⟨f, hf, u, hu, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
    change ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1
      (f.baseChange ℂ (a • ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ))) ∈
        Cm.cmLineSpan K X H v τ
    rw [map_smul, map_smul]
    exact (Cm.cmLineSpan K X H v τ).smul_mem a (Submodule.subset_span ⟨f, hf, rfl⟩)
  exact hs hθ

theorem raw_span_conjugation
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (τ : Gal(K/ℚ)) (θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθ : θ ∈ rawCMLineSpan K X H v τ) :
    ComplexMultiplication.WeightOne.CM.coefficientConjugation (X.rationalCohomology 1) θ ∈
      rawCMLineSpan K X H v (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) := by
  induction hθ using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨f, hf, u, hu, rfl⟩ := hz
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
      rw [← ComplexMultiplication.WeightOne.CM.baseChange_coefficientConjugation, ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_smul,
        coefficient_conjugation_embedding, ← ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv_conjugation]
      exact Submodule.subset_span ⟨f, hf, _, Submodule.smul_mem _ _
        (Submodule.mem_span_singleton_self _), rfl⟩
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
      rw [map_add]
      exact Submodule.add_mem _ ihx ihy
  | smul a x hx ih =>
      rw [ComplexMultiplication.EmbeddingHodgeType.CM.coefficientConjugation_smul]
      exact Submodule.smul_mem _ _ ih

theorem raw_span_to_conjugate_betti
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (X.rationalCohomology 1))
    (v : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (τ : Gal(K/ℚ)) (θ : ComplexMultiplication.WeightOne.CM.Complexification (X.rationalCohomology 1))
    (hθ : θ ∈ rawCMLineSpan K X H v τ) :
    ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1 θ) ∈
      Cm.cmLineSpan K X H v (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * τ) := by
  rw [← Albanese.HodgeComparisonIs.CM.Construction.complexification_conjugation]
  exact raw_span_to_betti K X H v _ _ (raw_span_conjugation K X H v τ θ hθ)

end

/-! Apply the full HeckeCycles proposition to finitely many fixed theta inputs on
one surface family. A product of the resulting thresholds gives one positive
common principal level, and all deeper multiples retain the exact CM spans. -/

open scoped Classical BigOperators

theorem p41_finite_family_common_level
    (hHeckeCycles : HeckeCyclesInput)
    (K : IntermediateField ℚ ℂ)
    [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
    {ι : Type} [Fintype ι]
    (v : ι → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (hv : ∀ i, (v i).val 1 = true)
    (Nbase : ℕ) (hNbase : 0 < Nbase)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (H : ∀ N, ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure ((X N).rationalCohomology 1))
    (hH : ∀ N, Albanese.HodgeComparisonIs.CM.Construction.IsCanonicalH1 (X N) (H N))
    (Θ : ι → ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : ∀ i, HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K
      (fun τ => (v i).val τ⁻¹) Nbase X (Θ i)) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ Nbase ∣ N₀ ∧
      ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ i,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1 (Θ i N) ∈
          Cm.cmLineSpan K (X N) (H N) (v i) 1 ∧
        ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 (X N)
            (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (X N).toOver) 1 (Θ i N)) ∈
          Cm.cmLineSpan K (X N) (H N) (v i) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) := by
  choose n hn hbase hextract using fun i =>
    hHeckeCycles K (v i) (hv i) (fun τ => (v i).val τ⁻¹) (fun _ => rfl)
      Nbase hNbase X H hH (Θ i) (hsource i)
  let N₀ := 3 * Nbase * ∏ i, n i
  have hprod : 0 < ∏ i, n i := Finset.prod_pos (fun i _ => hn i)
  have hlarge : 3 ≤ N₀ := by
    dsimp [N₀]
    nlinarith
  refine ⟨N₀, hlarge, dvd_mul_of_dvd_left (dvd_mul_left Nbase 3) _, ?_⟩
  intro N hN hdiv i
  have hi : n i ∣ N₀ := dvd_mul_of_dvd_right
    (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) _
  have hx : Θ i N ∈ rawCMLineSpan K (X N) (H N) (v i) 1 :=
    hextract i N hN (hi.trans hdiv)
  refine ⟨raw_span_to_betti K (X N) (H N) (v i) 1 (Θ i N) hx, ?_⟩
  simpa only [mul_one] using
    raw_span_to_conjugate_betti K (X N) (H N) (v i) 1 (Θ i N) hx

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HeckeCycles.CM
