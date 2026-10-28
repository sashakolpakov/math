import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Cm

/-! # Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Extraction.CM

noncomputable section

section

/-! The multilinear expansion step, independent of the main existence claim.
The pairing is the actual evaluation on the constructed surface fundamental
class. CM extraction and algebraic realization are separate prerequisites.
-/

/-- A nonzero bilinear pairing of spans has a nonzero pair of generators. -/
theorem exists_pair_of_span
    {U V : Type*} [AddCommGroup U] [Module ℂ U]
    [AddCommGroup V] [Module ℂ V]
    (B : U →ₗ[ℂ] V →ₗ[ℂ] ℂ) (s : Set U) (t : Set V)
    (x : U) (y : V)
    (hx : x ∈ Submodule.span ℂ s) (hy : y ∈ Submodule.span ℂ t)
    (hxy : B x y ≠ 0) :
    ∃ a ∈ s, ∃ b ∈ t, B a b ≠ 0 := by
  classical
  by_contra h
  push Not at h
  have ha : ∀ a ∈ s, y ∈ LinearMap.ker (B a) := by
    intro a ha
    apply (Submodule.span_le.mpr (show t ⊆ LinearMap.ker (B a) from ?_)) hy
    intro b hb
    exact h a ha b hb
  have hker : x ∈ LinearMap.ker ((LinearMap.applyₗ' ℂ y).comp B) := by
    apply (Submodule.span_le.mpr (show s ⊆
      LinearMap.ker ((LinearMap.applyₗ' ℂ y).comp B) from ?_)) hx
    intro a has
    exact ha a has
  exact hxy hker

/-- The source's nonzero pairing selects four individual one-form classes.
There is no arbitrary integration functional in this helper. -/
theorem exists_four_wedge_generators
    (S : Cm.ProjectiveSurface)
    (Θ : Fin 4 → Submodule ℂ (S.variety.complexCohomology 1))
    (ξ η : S.variety.complexCohomology 2)
    (hξ : ξ ∈ Cm.wedgeSpan S.variety (Θ 0) (Θ 1))
    (hη : η ∈ Cm.wedgeSpan S.variety (Θ 2) (Θ 3))
    (hnonzero : S.evaluate (Cm.cup S.variety 2 2 ξ η) ≠ 0) :
    ∃ a ∈ Θ 0, ∃ b ∈ Θ 1, ∃ c ∈ Θ 2, ∃ d ∈ Θ 3,
      S.evaluate (Cm.cup S.variety 2 2
        (Cm.cup S.variety 1 1 a b) (Cm.cup S.variety 1 1 c d)) ≠ 0 := by
  obtain ⟨x, ⟨a, ha, b, hb, rfl⟩, y, ⟨c, hc, d, hd, rfl⟩, h⟩ :=
    exists_pair_of_span ((Cm.cup S.variety 2 2).compr₂ S.evaluate)
      _ _ ξ η hξ hη hnonzero
  exact ⟨a, ha, b, hb, c, hc, d, hd, h⟩

end

/-! Extract individual rational Hodge-line images from a nonzero product. -/

open _root_.CategoryTheory

def fourValue (S : Cm.ProjectiveSurface)
    (a : Fin 4 → S.variety.complexCohomology 1) : ℂ :=
  S.evaluate (Cm.cup S.variety 2 2
    (Cm.cup S.variety 1 1 (a 0) (a 1)) (Cm.cup S.variety 1 1 (a 2) (a 3)))

theorem exists_generator_of_span
    {U : Type*} [AddCommGroup U] [Module ℂ U]
    (B : U →ₗ[ℂ] ℂ) (s : Set U) (x : U)
    (hx : x ∈ Submodule.span ℂ s) (h : B x ≠ 0) :
    ∃ a ∈ s, B a ≠ 0 := by
  classical
  by_contra hn
  push Not at hn
  have hz : x ∈ LinearMap.ker B :=
    (Submodule.span_le.mpr (show s ⊆ LinearMap.ker B from hn)) hx
  exact h hz

theorem exists_four_of_spans
    (S : Cm.ProjectiveSurface)
    (s : Fin 4 → Set (S.variety.complexCohomology 1))
    (a : Fin 4 → S.variety.complexCohomology 1)
    (ha : ∀ i, a i ∈ Submodule.span ℂ (s i))
    (hn : fourValue S a ≠ 0) :
    ∃ b ∈ s 0, ∃ c ∈ s 1, ∃ d ∈ s 2, ∃ e ∈ s 3,
      fourValue S ![b, c, d, e] ≠ 0 := by
  let B := (Cm.cup S.variety 2 2).compr₂ S.evaluate
  let W := Cm.cup S.variety 1 1
  obtain ⟨b, hb, hn0⟩ := exists_generator_of_span
    ((B.flip (W (a 2) (a 3))).comp (W.flip (a 1))) (s 0) (a 0) (ha 0) hn
  obtain ⟨c, hc, hn1⟩ := exists_generator_of_span
    ((B.flip (W (a 2) (a 3))).comp (W b)) (s 1) (a 1) (ha 1) hn0
  obtain ⟨d, hd, hn2⟩ := exists_generator_of_span
    ((B (W b c)).comp (W.flip (a 3))) (s 2) (a 2) (ha 2) hn1
  obtain ⟨e, he, hn3⟩ := exists_generator_of_span
    ((B (W b c)).comp (W d)) (s 3) (a 3) (ha 3) hn2
  exact ⟨b, hb, c, hc, d, hd, e, he, hn3⟩

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]

def slotLabel (i : Fin 4) : Gal(K/ℚ) :=
  if i.val < 2 then 1 else ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K

def hodgeLineImage (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : K →ₗ[ℚ] X.rationalCohomology 1) (τ : Gal(K/ℚ)) :
    X.complexCohomology 1 :=
  ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace X.toOver) 1
    (u.baseChange ℂ (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K τ)))

/-- The selected term retains the actual rational Hodge maps and 1,1,c,c vectors. -/
theorem exists_nonzero_hodge_line_term
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (S : Cm.ProjectiveSurface)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (S.variety.rationalCohomology 1))
    (a : Fin 4 → S.variety.complexCohomology 1)
    (ha : ∀ i, a i ∈ Cm.cmLineSpan K S.variety H (v i) (slotLabel K i))
    (hn : fourValue S a ≠ 0) :
    ∃ u : Fin 4 → (K →ₗ[ℚ] S.variety.rationalCohomology 1),
      (∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)) H (u i)) ∧
      fourValue S (fun i => hodgeLineImage K S.variety (u i) (slotLabel K i)) ≠ 0 := by
  obtain ⟨b, ⟨u0, hu0, rfl⟩, c, ⟨u1, hu1, rfl⟩,
      d, ⟨u2, hu2, rfl⟩, e, ⟨u3, hu3, rfl⟩, hn⟩ :=
    exists_four_of_spans S
      (fun i => {z | ∃ u : K →ₗ[ℚ] S.variety.rationalCohomology 1,
        ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)) H u ∧
        z = hodgeLineImage K S.variety u (slotLabel K i)}) a ha hn
  refine ⟨![u0, u1, u2, u3], ?_, hn⟩
  intro i
  fin_cases i <;> assumption

/-- Combine factorization and line-span extraction without introducing any
global surface or CM-extraction existence hypothesis. -/
theorem exists_hodge_term_of_wedge_spans
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (S : Cm.ProjectiveSurface)
    (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure (S.variety.rationalCohomology 1))
    (Θ : Fin 4 → Submodule ℂ (S.variety.complexCohomology 1))
    (hCM : ∀ i, Θ i ≤ Cm.cmLineSpan K S.variety H (v i) (slotLabel K i))
    (ξ η : S.variety.complexCohomology 2)
    (hξ : ξ ∈ Cm.wedgeSpan S.variety (Θ 0) (Θ 1))
    (hη : η ∈ Cm.wedgeSpan S.variety (Θ 2) (Θ 3))
    (hn : S.evaluate (Cm.cup S.variety 2 2 ξ η) ≠ 0) :
    ∃ u : Fin 4 → (K →ₗ[ℚ] S.variety.rationalCohomology 1),
      (∀ i, ComplexMultiplication.WeightOne.CM.IsHodgeMap (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)) H (u i)) ∧
      fourValue S (fun i => hodgeLineImage K S.variety (u i) (slotLabel K i)) ≠ 0 := by
  obtain ⟨a, ha, b, hb, c, hc, d, hd, hn⟩ :=
    exists_four_wedge_generators S Θ ξ η hξ hη hn
  refine exists_nonzero_hodge_line_term K v S H ![a, b, c, d] ?_ hn
  intro i
  fin_cases i
  · exact hCM 0 ha
  · exact hCM 1 hb
  · exact hCM 2 hc
  · exact hCM 3 hd

def pulledEmbedding
    (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))
    (X : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (f : (i : Fin 4) → X.toOver ⟶ (R i).abelianVariety.toOver)
    (i : Fin 4) : X.complexCohomology 1 :=
  Betti.Scheme.schemeBettiMap (ModuleCat.of ℂ ℂ) 1 (f i)
    ((R i).complexComparison
      (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingVector K (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv K (slotLabel K i))))

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Extraction.CM
