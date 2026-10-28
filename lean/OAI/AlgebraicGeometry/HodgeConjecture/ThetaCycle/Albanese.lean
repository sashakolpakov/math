import OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Denominators

/-! # Albanese -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Albanese.CM

noncomputable section

section

/-! Algebraic realization on an already-given surface. The named DegreeTwo input
is its full original weight-one proposition; ConstructionInput and HodgeComparisonInput are the
full source-pinned propositions from DegreeTwo. No statement stub is imported.
The global ThetaCycle existence statement is not changed or used here. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions

/-- Exactly the full original DegreeTwo weight-one clause, before specializing A,B. -/
def WeightOneInput : Prop :=
  ∀ (A B : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety)
    (u : A.variety.rationalCohomology 1 →ₗ[ℚ] B.variety.rationalCohomology 1),
    (∀ x ∈ A.h1Holomorphic, u.baseChange ℂ x ∈ B.h1Holomorphic) →
    (∀ x ∈ A.h1Antiholomorphic, u.baseChange ℂ x ∈ B.h1Antiholomorphic) →
    ∃ n : ℕ, 0 < n ∧ ∃ g : B.toOver ⟶ A.toOver,
      IsMonHom g ∧ ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g = (n : ℚ) • u

/-- Actual rational cohomology pullback respects composition of scheme maps. -/
theorem rational_betti_comp {X Y Z : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety}
    (a : X.toOver ⟶ Y.toOver) (g : Y.toOver ⟶ Z.toOver) :
    (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (a ≫ g)).hom =
      (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 a).hom.comp
        (Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 g).hom := by
  ext x
  exact ConcreteCategory.congr_hom
    ((Betti.Scheme.schemeBettiFunctor (ModuleCat.of ℚ ℚ) 1).map_comp g.op a.op) x

/-- Construction/HodgeComparison and full DegreeTwo construct an actual map from the surface.
Its rational pullback is a positive integral multiple of the given Hodge map. -/
theorem surface_hodge_map_algebraic
    (hDegreeTwo : WeightOneInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput) (hHodgeComparison : DegreeTwo.Transport.Constructions.HodgeComparisonInput)
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
  classical
  let x₀ : S.variety.analyticSpace := Classical.choice inferInstance
  obtain ⟨A, a, ha₀, haU⟩ := hConstruction S.variety.presentation x₀
  have ha : DegreeTwo.Transport.Constructions.IsAlbaneseMap S.variety x₀ A a := by
    simpa only [DegreeTwo.Transport.Constructions.IsAlbaneseMap, MonObj.one_eq_one] using And.intro ha₀ haU
  obtain ⟨HA, HX, e, hA, hX, he, hforward, hinverse⟩ := hHodgeComparison S.variety x₀ A a ha
  have hi : ComplexMultiplication.WeightOne.CM.IsHodgeMap H HA e.symm.toLinearMap := by
    intro x hx
    apply hinverse x
    rw [hX.1, ← hH.1]
    exact hx
  let t := e.symm.toLinearMap.comp (u.comp R.comparison.symm.toLinearMap)
  have ht : ComplexMultiplication.WeightOne.CM.IsHodgeMap R.h1HodgeStructure HA t :=
    hi.comp (hu.comp (J.transport_symm_isHodgeMap R.comparison))
  obtain ⟨n, hn, g, hg, hgpull⟩ := hDegreeTwo R.abelianVariety A t
    (fun x hx => by
      change t.baseChange ℂ x ∈ A.h1Holomorphic
      change t.baseChange ℂ x ∈ (A.variety.pureBettiSubspace 1 0).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1)
      rw [← hA.1]
      exact ht x (R.h1HodgeStructure_holomorphic.symm ▸ hx))
    (fun x hx => by
      change t.baseChange ℂ x ∈ (A.variety.pureBettiSubspace 0 1).comap
        (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace A.toOver) 1)
      rw [← hA.2]
      exact ht.map_antiholomorphic (R.h1HodgeStructure_antiholomorphic.symm ▸ hx))
  refine ⟨n, hn, a ≫ g, ?_⟩
  rw [rational_betti_comp, ← he]
  change e.toLinearMap.comp ((ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety.h1Pullback g).comp
    R.comparison.toLinearMap) = _
  rw [hgpull]
  ext x
  change e ((n : ℚ) • e.symm (u (R.comparison.symm (R.comparison x)))) = (n : ℚ) • u x
  rw [R.comparison.symm_apply_apply, map_smul, e.apply_symm_apply]

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
  (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))

/-- Assemble the four actual algebraic maps from the extracted term. -/
theorem algebraic_maps_of_hodge_term
    (hDegreeTwo : WeightOneInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput) (hHodgeComparison : DegreeTwo.Transport.Constructions.HodgeComparisonInput)
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
  classical
  choose n hnpos f hf using fun i => surface_hodge_map_algebraic
    hDegreeTwo hConstruction hHodgeComparison (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)) (R i) S H hH (u i) (hu i)
  let r : Fin 4 → ℚ := fun i => (n i : ℚ)⁻¹
  have hnu (i : Fin 4) : (n i : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hnpos i))
  have hr : ∀ i, u i = r i •
      ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (f i)).hom.comp (R i).comparison.toLinearMap) := by
    intro i
    rw [hf i, smul_smul, inv_mul_cancel₀ (hnu i), one_smul]
  obtain ⟨D, hD, k, hk, hclear, hnonzero⟩ :=
    Denominators.CM.realized_hodge_term_nonzero K v R S f u r hr hn
  refine ⟨f, n, hnpos, hf, ?_, hnonzero⟩
  intro i
  have hline := Denominators.CM.hodgeLineImage_rational_pullback K v R S f u r hr i
  rw [hline, smul_smul]
  have hc : (n i : ℂ) * (r i : ℂ) = 1 := by
    change (n i : ℂ) * (((n i : ℚ)⁻¹ : ℚ) : ℂ) = 1
    rw [Rat.cast_inv, Rat.cast_natCast, mul_inv_cancel₀]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (hnpos i))
  rw [hc, one_smul]

/-- Independent conditional ThetaCycle assembly on a given native surface and its
derived wedge data. Global surface and CM-extraction existence are not inputs
to the accepted main target, and that target is neither changed nor invoked. -/
theorem algebraic_maps_of_wedge_data
    (hDegreeTwo : WeightOneInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput) (hHodgeComparison : DegreeTwo.Transport.Constructions.HodgeComparisonInput)
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
  obtain ⟨u, hu, hterm⟩ := Extraction.CM.exists_hodge_term_of_wedge_spans K v S H Θ hCM ξ ζ hξ hη hn
  obtain ⟨f, n, hnpos, hQ, hC, hnonzero⟩ :=
    algebraic_maps_of_hodge_term K v R hDegreeTwo hConstruction hHodgeComparison S H hH u hu hterm
  exact ⟨f, hnonzero⟩

end

/-! DegreeTwo's accepted conditional weight-one clause at
8f9a5322070d96e94664a78a4b3c19806875f1c2. Its HolomorphicAlgebraicity, Construction, and HodgeComparison conditions
remain explicit. The ThetaCycle target concerns maps and degree-one pullbacks;
DegreeTwo's separate degree-two cycle-existence clause is not used by this adapter. -/

open OAI.AlgebraicGeometry.HodgeConjecture.DegreeTwo.Transport.Constructions

def ConditionalWeightOneInput : Prop :=
  DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput → DegreeTwo.Transport.Constructions.ConstructionInput → DegreeTwo.Transport.Constructions.HodgeComparisonInput → WeightOneInput

theorem p23_weight_one_of_conditional (hDegreeTwo : ConditionalWeightOneInput)
    (hHolomorphicAlgebraicity : DegreeTwo.Transport.Constructions.HolomorphicAlgebraicityInput) (hConstruction : DegreeTwo.Transport.Constructions.ConstructionInput) (hHodgeComparison : DegreeTwo.Transport.Constructions.HodgeComparisonInput) : WeightOneInput :=
  hDegreeTwo hHolomorphicAlgebraicity hConstruction hHodgeComparison

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Albanese.CM
