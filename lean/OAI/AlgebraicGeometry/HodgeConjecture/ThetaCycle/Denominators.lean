import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Extraction

/-! # Denominators -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Denominators.CM

noncomputable section

/-! Clear rational coefficients on already-given algebraic pullbacks while
retaining the actual morphisms, embedding vectors, and nonzero evaluation. -/

open _root_.CategoryTheory
open scoped BigOperators

theorem fourValue_smul (S : Cm.ProjectiveSurface)
    (r : Fin 4 → ℂ) (a : Fin 4 → S.variety.complexCohomology 1) :
    Extraction.CM.fourValue S (fun i => r i • a i) =
      (r 0 * r 1 * r 2 * r 3) * Extraction.CM.fourValue S a := by
  simp only [Extraction.CM.fourValue, map_smul, LinearMap.smul_apply, smul_smul,
    smul_eq_mul, mul_assoc]
  ring

/-- A positive common denominator for the four explicit rational scalars. -/
theorem common_positive_denominator (r : Fin 4 → ℚ) :
    ∃ D : ℕ, 0 < D ∧ ∃ k : Fin 4 → ℤ, ∀ i, (D : ℚ) * r i = (k i : ℚ) := by
  classical
  let D := ∏ i : Fin 4, (r i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (r i).den_pos)
  have hi : ∀ i : Fin 4, ∃ k : ℤ, (D : ℚ) * r i = (k : ℚ) := by
    intro i
    have hdiv : (r i).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
    obtain ⟨b, hb⟩ := hdiv
    have hr : r i * (r i).den = ((r i).num : ℚ) :=
      (eq_div_iff (Nat.cast_ne_zero.mpr (r i).den_ne_zero)).mp (Rat.num_div_den (r i)).symm
    refine ⟨(b : ℤ) * (r i).num, ?_⟩
    calc
      (D : ℚ) * r i = (b : ℚ) * (r i * (r i).den) := by rw [hb, Nat.cast_mul]; ring
      _ = (((b : ℤ) * (r i).num : ℤ) : ℚ) := by
        rw [hr]
        simp only [Int.cast_mul, Int.cast_natCast]
  choose k hk using hi
  exact ⟨D, hD, k, hk⟩

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [NumberField.IsCMField K]
  (v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
  (R : ∀ i, ComplexMultiplication.CMKnownResults.CM.HodgeRealization (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.hodgeStructure K (v i)))

/-- Identify a rational Hodge-line image with a rational multiple of the
actual algebraic pullback, through the native scalar-extension comparison. -/
theorem hodgeLineImage_rational_pullback
    (S : Cm.ProjectiveSurface)
    (f : (i : Fin 4) → S.variety.toOver ⟶ (R i).abelianVariety.toOver)
    (u : Fin 4 → (K →ₗ[ℚ] S.variety.rationalCohomology 1))
    (r : Fin 4 → ℚ)
    (hu : ∀ i, u i = r i •
      ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (f i)).hom.comp
        (R i).comparison.toLinearMap)) (i : Fin 4) :
    Extraction.CM.hodgeLineImage K S.variety (u i) (Extraction.CM.slotLabel K i) =
      (r i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i := by
  unfold Extraction.CM.hodgeLineImage
  rw [hu i, LinearMap.baseChange_smul, LinearMap.smul_apply,
    ← Rat.cast_smul_eq_qsmul ℂ (r i), map_smul,
    LinearMap.baseChange_comp, LinearMap.comp_apply,
    HeckeCycles.GeometricSource.CM.complexification_pullback]
  rfl

/-- Rational homomorphism coefficients can be cleared; the same four actual
algebraic maps already have nonzero product evaluation. -/
theorem clear_rational_pullback_denominators
    (S : Cm.ProjectiveSurface)
    (f : (i : Fin 4) → S.variety.toOver ⟶ (R i).abelianVariety.toOver)
    (r : Fin 4 → ℚ)
    (hn : Extraction.CM.fourValue S
      (fun i => (r i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i) ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ ∃ k : Fin 4 → ℤ,
      (∀ i, (D : ℚ) * r i = (k i : ℚ)) ∧
      Extraction.CM.fourValue S (fun i => (k i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i) ≠ 0 ∧
      S.evaluate (Cm.fourClass K v R S.variety f) ≠ 0 := by
  obtain ⟨D, hD, k, hk⟩ := common_positive_denominator r
  have hDC : (D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hD)
  have heq : (fun i => (k i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i) =
      (fun i => (D : ℂ) • ((r i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i)) := by
    funext i
    have hi : (k i : ℂ) = (D : ℂ) * (r i : ℂ) := by exact_mod_cast (hk i).symm
    rw [hi, smul_smul]
  refine ⟨D, hD, k, hk, ?_, ?_⟩
  · rw [heq, fourValue_smul]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hDC hDC) hDC) hDC) hn
  · intro hz
    apply hn
    rw [fourValue_smul]
    change _ * S.evaluate (Cm.fourClass K v R S.variety f) = 0
    rw [hz, mul_zero]

/-- Once the rational Hodge maps have been realized by given algebraic maps,
the selected nonzero term yields a nonzero product on those very maps. -/
theorem realized_hodge_term_nonzero
    (S : Cm.ProjectiveSurface)
    (f : (i : Fin 4) → S.variety.toOver ⟶ (R i).abelianVariety.toOver)
    (u : Fin 4 → (K →ₗ[ℚ] S.variety.rationalCohomology 1))
    (r : Fin 4 → ℚ)
    (hu : ∀ i, u i = r i •
      ((Betti.Scheme.schemeBettiMap (ModuleCat.of ℚ ℚ) 1 (f i)).hom.comp
        (R i).comparison.toLinearMap))
    (hn : Extraction.CM.fourValue S
      (fun i => Extraction.CM.hodgeLineImage K S.variety (u i) (Extraction.CM.slotLabel K i)) ≠ 0) :
    ∃ D : ℕ, 0 < D ∧ ∃ k : Fin 4 → ℤ,
      (∀ i, (D : ℚ) * r i = (k i : ℚ)) ∧
      Extraction.CM.fourValue S (fun i => (k i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i) ≠ 0 ∧
      S.evaluate (Cm.fourClass K v R S.variety f) ≠ 0 := by
  have heq : (fun i => Extraction.CM.hodgeLineImage K S.variety (u i) (Extraction.CM.slotLabel K i)) =
      (fun i => (r i : ℂ) • Extraction.CM.pulledEmbedding K v R S.variety f i) := by
    funext i
    exact hodgeLineImage_rational_pullback K v R S f u r hu i
  rw [heq] at hn
  exact clear_rational_pullback_denominators K v R S f r hn

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.Denominators.CM
