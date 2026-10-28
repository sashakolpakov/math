import OAI.RepresentationTheory.Hecke.RadialDilation.Cm

/-! # Analytic Dilation -/

namespace OAI.RepresentationTheory.Hecke.RadialDilation.AnalyticDilation.Analytic

noncomputable section

/-! The elementary scalar calculation, separated from the historical graph contract.
This proof repeats the checked elementary calculation so that the historical
statement and proof remain byte-for-byte unchanged. The native entry point
constructs every analytic hypothesis of this helper. -/

open scoped Classical
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm

private abbrev Qbar : IntermediateField ℚ ℂ := _root_.algebraicClosure ℚ ℂ

private def allEmbeddingUnits (z : ℂ) : Prop :=
  ∃ a : Qbar, (a : ℂ) = z ∧
    ∀ σ : Qbar →ₐ[ℚ] ℂ, ‖σ a‖ = 1

private lemma allEmbeddingUnits.algebraic {z : ℂ}
    (hz : Analytic.allEmbeddingUnits z) : IsAlgebraic ℚ z := by
  obtain ⟨a, rfl, _⟩ := hz
  exact a.property.isAlgebraic

private lemma allEmbeddingUnits.one : Analytic.allEmbeddingUnits 1 := by
  exact ⟨1, rfl, fun σ => by simp⟩

private lemma allEmbeddingUnits.mul {z w : ℂ}
    (hz : Analytic.allEmbeddingUnits z) (hw : Analytic.allEmbeddingUnits w) :
    Analytic.allEmbeddingUnits (z * w) := by
  obtain ⟨a, rfl, ha⟩ := hz
  obtain ⟨b, rfl, hb⟩ := hw
  exact ⟨a * b, rfl, fun σ => by simp [ha σ, hb σ]⟩

private lemma allEmbeddingUnits.zpow {z : ℂ}
    (hz : Analytic.allEmbeddingUnits z) (n : ℤ) : Analytic.allEmbeddingUnits (z ^ n) := by
  obtain ⟨a, rfl, ha⟩ := hz
  exact ⟨a ^ n, map_zpow₀ Qbar.val a n, fun σ => by simp [norm_zpow, ha σ]⟩

private lemma allEmbeddingUnits.prod {ι : Type*} (s : Finset ι)
    (f : ι → ℂ) (hf : ∀ i ∈ s, Analytic.allEmbeddingUnits (f i)) :
    Analytic.allEmbeddingUnits (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using Analytic.allEmbeddingUnits.one
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      exact (Analytic.allEmbeddingUnits.mul (hf i (Finset.mem_insert_self i s)))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

private lemma allEmbeddingUnits.of_pow {z : ℂ} {n : ℕ} (hn : 0 < n)
    (hz : Analytic.allEmbeddingUnits (z ^ n)) : Analytic.allEmbeddingUnits z := by
  obtain ⟨b, hb, hbunit⟩ := hz
  have halg : IsAlgebraic ℚ z :=
    IsAlgebraic.of_pow hn (hb ▸ b.property.isAlgebraic)
  let a : Qbar := ⟨z, halg.isIntegral⟩
  have hab : a ^ n = b := by
    apply Subtype.ext
    exact hb.symm
  refine ⟨a, rfl, fun σ => ?_⟩
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp
  rw [← norm_pow, ← map_pow, hab, hbunit]

private lemma allEmbeddingUnits.to_minpoly {z : ℂ}
    (hz : Analytic.allEmbeddingUnits z) : Cm.algebraicUnitCircle z := by
  refine ⟨(Analytic.allEmbeddingUnits.algebraic hz), ?_⟩
  obtain ⟨a, rfl, ha⟩ := hz
  intro w hw
  have hroot : Polynomial.aeval w (minpoly ℚ a) = 0 := by
    have he := minpoly.algHom_eq Qbar.val Qbar.val.injective a
    change minpoly ℚ (a : ℂ) = minpoly ℚ a at he
    rw [← he]
    exact hw
  obtain ⟨σ, hσ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
    (fun x : Qbar => ⟨(isIntegral_algHom_iff Qbar.val Qbar.val.injective).mp
      x.property, IsAlgClosed.splits _⟩) hroot
  change σ a = w at hσ
  rw [← hσ]
  exact ha σ

private lemma finitePhase.ne_zero {z : ℂ} (hz : Cm.finitePhase z) : z ≠ 0 := by
  obtain ⟨n, hn, he⟩ := hz
  intro h
  simp [h, zero_pow hn.ne'] at he

private lemma finitePhase.zpow {z : ℂ} (hz : Cm.finitePhase z) (k : ℤ) :
    Cm.finitePhase (z ^ k) := by
  obtain ⟨n, hn, he⟩ := hz
  refine ⟨n, hn, ?_⟩
  rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul,
    zpow_natCast, he, one_zpow]

private lemma finitePhase.allEmbeddingUnits {z : ℂ} (hz : Cm.finitePhase z) :
    Analytic.allEmbeddingUnits z := by
  obtain ⟨n, hn, he⟩ := hz
  exact Analytic.allEmbeddingUnits.of_pow hn (he ▸ Analytic.allEmbeddingUnits.one)

private lemma cm_embedding_unit
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [NumberField.IsCMField E]
    (r : Eˣ)
    (hnorm : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (ρ : E →ₐ[ℚ] ℂ) : Analytic.allEmbeddingUnits (ρ (r : E)) := by
  let j : E →ₐ[ℚ] Qbar := ρ.codRestrict _ (fun x =>
    ((Algebra.IsIntegral.isIntegral x).map ρ))
  refine ⟨j (r : E), rfl, fun σ => ?_⟩
  let φ : E →ₐ[ℚ] ℂ := σ.comp j
  have he := congrArg φ hnorm
  rw [map_mul, map_one] at he
  have hc : φ (AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E)) = star (φ (r : E)) :=
    AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.embedding_conjugation E φ.toRingHom (r : E)
  rw [hc] at he
  have hn := congrArg norm he
  simp only [norm_mul, norm_star, norm_one] at hn
  change ‖φ (r : E)‖ = 1
  nlinarith [norm_nonneg (φ (r : E))]

private lemma dilation_pow_formula
    (q : ℕ) [Fact q.Prime]
    (D : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q)
    (hD : ∀ b x,
      (D b).val x =
        (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) *
          b.val (fun i => (q : ℚ_[q])⁻¹ * x i))
    (n : ℕ) (b : Cm.radialInput q) (x : Fin 3 → ℚ_[q]) :
    ((D ^ n) b).val x =
      (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) ^ n *
        b.val (fun i => ((q : ℚ_[q]) ^ n)⁻¹ * x i) := by
  induction n generalizing b x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, hD, ih]
      simp only [pow_succ, mul_inv_rev]
      have hx : (fun i => ((q : ℚ_[q]) ^ n)⁻¹ * ((q : ℚ_[q])⁻¹ * x i)) =
          (fun i => (q : ℚ_[q])⁻¹ * ((q : ℚ_[q]) ^ n)⁻¹ * x i) := by
        funext i
        ring
      rw [hx]
      ring

private lemma local_eq_dilation_pow
    (q : ℕ) [Fact q.Prime] (M : ℕ)
    (D Uq : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q)
    (hD : ∀ b x,
      (D b).val x =
        (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) *
          b.val (fun i => (q : ℚ_[q])⁻¹ * x i))
    (hUq : ∀ b x,
      (Uq b).val x =
        (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
          b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i)) :
    Uq = D ^ M := by
  ext b x
  rw [hUq, dilation_pow_formula q D hD]
  have he : (3 : ℝ) * M / 2 = (3 / 2 : ℝ) * (M : ℝ) := by ring
  rw [he]
  have hr := Real.rpow_mul (show 0 ≤ (q : ℝ) from Nat.cast_nonneg q)
    (3 / 2 : ℝ) (M : ℝ)
  rw [Real.rpow_natCast] at hr
  change Real.rpow (q : ℝ) ((3 / 2 : ℝ) * (M : ℝ)) =
    Real.rpow (q : ℝ) (3 / 2 : ℝ) ^ M at hr
  rw [hr, Complex.ofReal_pow]

private lemma archimedean_square
    {ι : Type*} [DecidableEq ι] (active : ι) (reps : Finset ι)
    (hactive : active ∈ reps) (a : ι → ℂ) (d : ι → ℤ)
    (hd : d active = 1) (halfDet : ℂ)
    (hdet : halfDet ^ 2 = a active ^ (1 - 2 : ℤ) *
      ∏ τ ∈ reps.erase active, a τ ^ (-3 * d τ)) :
    (halfDet * (a active)⁻¹) ^ 2 =
      ∏ τ ∈ reps, a τ ^ (-3 * d τ) := by
  rw [mul_pow, hdet, ← Finset.mul_prod_erase reps _ hactive, hd]
  norm_num
  ring

private lemma signed_product
    {ι : Type*} (reps : Finset ι) (a : ι → ℂ) (d : ι → ℤ)
    (ε : ℤ) :
    (∏ τ ∈ reps, a τ ^ (-3 * d τ)) ^ (-ε) =
      ∏ τ ∈ reps, a τ ^ (ε * 3 * d τ) := by
  rw [← Finset.prod_zpow]
  apply Finset.prod_congr rfl
  intro τ _
  rw [← zpow_mul]
  congr 1
  ring

/-- The elementary analytic implication, with its local and theta identities explicit. -/
theorem algebraic_dilation_relation
    (E : IntermediateField ℚ ℂ)
    [NumberField E] [IsGalois ℚ E] [NumberField.IsCMField E]
    (v : AlgebraicGeometry.ComplexMultiplication.OddSignSwitch.CM.OddSignPattern
      (fun τ : Gal(E/ℚ) => AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ))
    (hv : v.val 1 = true)
    (d : Gal(E/ℚ) → ℤ)
    (hd : ∀ τ, d τ = AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val τ⁻¹))
    (reps : Finset (Gal(E/ℚ)))
    (hactive : (1 : Gal(E/ℚ)) ∈ reps)
    (_hrepresentatives : ∀ τ : Gal(E/ℚ),
      τ ∈ reps ↔ AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E * τ ∉ reps)
    (r : Eˣ)
    (hnorm : (r : E) * AlgebraicGeometry.ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (r : E) = 1)
    (q : ℕ) [Fact q.Prime]
    (M : ℕ) (hM : 0 < M)
    (S V : Type*)
    [AddCommGroup S] [Module ℂ S]
    [AddCommGroup V] [Module ℂ V]
    (j : Cm.radialInput q →ₗ[ℂ] S)
    (_hj : Function.Injective j)
    (Θ : S →ₗ[ℂ] V)
    (U : S →ₗ[ℂ] S)
    (D Uq : Cm.radialInput q →ₗ[ℂ] Cm.radialInput q)
    (hD : ∀ b x,
      (D b).val x =
        (Real.rpow (q : ℝ) (3 / 2 : ℝ) : ℂ) *
          b.val (fun i => (q : ℚ_[q])⁻¹ * x i))
    (hUq : ∀ b x,
      (Uq b).val x =
        (Real.rpow (q : ℝ) (3 * (M : ℝ) / 2) : ℂ) *
          b.val (fun i => ((q : ℚ_[q]) ^ M)⁻¹ * x i))
    (ξ : ℂ) (hξ : Cm.finitePhase ξ)
    (hfinite : ∀ b, U (j b) = ξ • j (Uq b))
    (halfDet : ℂ)
    (hdet :
      halfDet ^ 2 =
        (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E)) ^ (1 - 2 : ℤ) *
          ∏ τ ∈ reps.erase 1,
            (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ))
    (ε : ℤ) (_hε : ε = 1 ∨ ε = -1)
    (hPoisson : ∀ f : S,
      Θ (U f) =
        ((halfDet *
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ (-ε)) •
            Θ f) :
    (halfDet *
      (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1 (r : E))⁻¹) ^ 2 =
        ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (-3 * d τ)
    ∧
    ∃ ω ζ : ℂ,
      Cm.finitePhase ζ ∧
      (∀ b : Cm.radialInput q,
        Θ (j ((D ^ M) b)) = ω • Θ (j b)) ∧
      ω ^ 2 =
        ζ * ∏ τ ∈ reps,
          (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)) ^ (ε * 3 * d τ) ∧
      Cm.algebraicUnitCircle ω ∧
      (∀ e₀ : ℂ, e₀ ^ M = ω → Cm.algebraicUnitCircle e₀) := by
  let a : Gal(E/ℚ) → ℂ := fun τ => AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ (r : E)
  let s : ℂ := halfDet * (a 1)⁻¹
  have hd1 : d 1 = 1 := by simp [hd, hv, AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue]
  have hsquare : s ^ 2 = ∏ τ ∈ reps, a τ ^ (-3 * d τ) :=
    archimedean_square 1 reps hactive a d hd1 halfDet hdet
  refine ⟨hsquare, ?_⟩
  have ha : ∀ τ, Analytic.allEmbeddingUnits (a τ) :=
    fun τ => cm_embedding_unit E r hnorm (AlgebraicGeometry.ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E τ)
  have hsunit : Analytic.allEmbeddingUnits s := by
    apply Analytic.allEmbeddingUnits.of_pow (n := 2) (by decide)
    rw [hsquare]
    exact Analytic.allEmbeddingUnits.prod reps _ (fun τ _ => (Analytic.allEmbeddingUnits.zpow (ha τ)) _)
  let ω : ℂ := ξ⁻¹ * s ^ (-ε)
  let ζ : ℂ := ξ ^ (-2 : ℤ)
  have hωunit : Analytic.allEmbeddingUnits ω := by
    have hi : Analytic.allEmbeddingUnits ξ⁻¹ := by
      simpa using (Analytic.allEmbeddingUnits.zpow (finitePhase.allEmbeddingUnits hξ)) (-1)
    exact (Analytic.allEmbeddingUnits.mul hi) ((Analytic.allEmbeddingUnits.zpow hsunit) (-ε))
  have hlocal : Uq = D ^ M := local_eq_dilation_pow q M D Uq hD hUq
  refine ⟨ω, ζ, Analytic.finitePhase.zpow hξ (-2), ?_, ?_, (Analytic.allEmbeddingUnits.to_minpoly hωunit), ?_⟩
  · intro b
    have hc := hPoisson (j b)
    rw [hfinite, map_smul, hlocal] at hc
    have he := congrArg (fun y : V => ξ⁻¹ • y) hc
    simpa only [smul_smul, inv_mul_cancel₀ (Analytic.finitePhase.ne_zero hξ), one_smul] using he
  · change (ξ⁻¹ * s ^ (-ε)) ^ 2 =
      ξ ^ (-2 : ℤ) * ∏ τ ∈ reps, a τ ^ (ε * 3 * d τ)
    have hp : (s ^ (-ε)) ^ 2 = (s ^ 2) ^ (-ε) := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm (-ε), zpow_mul, zpow_natCast]
    rw [mul_pow, hp, hsquare, signed_product]
    congr 1
    norm_num [zpow_neg, inv_pow]
  · intro e₀ he
    exact (Analytic.allEmbeddingUnits.to_minpoly (allEmbeddingUnits.of_pow hM (he ▸ hωunit)))

end

end OAI.RepresentationTheory.Hecke.RadialDilation.AnalyticDilation.Analytic
