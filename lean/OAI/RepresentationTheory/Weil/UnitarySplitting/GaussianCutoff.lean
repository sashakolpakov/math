import OAI.RepresentationTheory.Weil.UnitarySplitting.BilinearFourierPairing
import OAI.RepresentationTheory.Weil.UnitarySplitting.QuadraticCutoffTranslations

/-! # Gaussian Cutoff -/

namespace OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff.Construction

noncomputable section

section

/-! Stable compact Gaussian cutoffs determine the Fourier transform of
the oscillatory Gaussian on every compact test function. -/

open _root_.MeasureTheory

def HasGaussianCutoffs
    {F V : Type} [Field F] [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V]
    (μ : Measure V) (ψ : AddChar F ℂ) (q : V → F) (Γ : ℂ) : Prop :=
  ∀ K : Set V, IsCompact K → ∃ D : Set V, IsCompact D ∧ IsClopen D ∧ K ⊆ D ∧
    (∀ v ∈ K, ∀ x : V, v + x ∈ D ↔ x ∈ D) ∧
    (∫ x, D.indicator (fun x => ψ (q x)) x ∂μ) = Γ

theorem gaussianCutoff_fourier_pairing_comp
    {F V : Type} [NormedField F] [NormedAddCommGroup V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (ψ : AddChar F ℂ) (hc : Continuous (fun x : F => ψ x)) (hu : ∀ x : F, ‖ψ x‖ = 1)
    (μ : Measure V) [μ.IsAddHaarMeasure] [SigmaFinite μ]
    (q : V → F) (hq : Continuous q) (B : V → V → F)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hBs : ∀ x y, B x y = B y x)
    (hadd : ∀ v x, q (v + x) = q v + q x + B v x)
    (Γ : ℂ) (hΓ : HasGaussianCutoffs μ ψ q Γ)
    (L : V → V) (hL : Continuous L)
    (f : V → ℂ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (hFs : HasCompactSupport (fun x => ∫ y, ψ (B x (L y)) * f y ∂μ)) :
    (∫ x, ψ (q x) * (∫ y, ψ (B x (L y)) * f y ∂μ) ∂μ) =
      Γ * ∫ y, ψ (-q (L y)) * f y ∂μ := by
  classical
  let T : V → ℂ := fun x => ∫ y, ψ (B x (L y)) * f y ∂μ
  obtain ⟨D, hDc, hDo, hKD, hshift, hvalue⟩ := hΓ (L '' tsupport f ∪ tsupport T)
    ((hfs.image hL).union hFs)
  let k := D.indicator (fun x => ψ (q x))
  have hkc : Continuous k := hDo.continuous_indicator (hc.comp hq)
  have hks : HasCompactSupport k := HasCompactSupport.intro hDc
    (fun x hx => Set.indicator_of_notMem hx _)
  have hki : Integrable k μ := hkc.integrable_of_hasCompactSupport hks
  have hfi : Integrable f μ := hf.integrable_of_hasCompactSupport hfs
  have hcut : (fun x => ψ (q x) * T x) = fun x => k x * T x := by
    funext x
    by_cases hx : x ∈ D
    · simp only [k, Set.indicator_of_mem hx]
    · have htx : T x = 0 := image_eq_zero_of_notMem_tsupport
        (fun hh => hx (hKD (Or.inr hh)))
      rw [htx, mul_zero, mul_zero]
  change (∫ x, ψ (q x) * T x ∂μ) = _
  rw [hcut, BilinearFourierPairing.Construction.bilinear_fourier_pairing ψ hc hu (fun x y => B x (L y))
    (hB.comp (continuous_fst.prodMk (hL.comp continuous_snd))) μ f k hf hkc hfi hki]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    by_cases hy : y ∈ tsupport f
    · have heq : (∫ x, ψ (B x (L y)) * k x ∂μ) = ψ (-q (L y)) * Γ := by
        calc
          _ = ∫ x, D.indicator (fun x => ψ (q x + B (L y) x)) x ∂μ := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun x => by
              dsimp only [k]
              by_cases hx : x ∈ D
              · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, ψ.map_add_eq_mul, hBs x (L y)]
                ring
              · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
          _ = _ := by
            rw [QuadraticCutoffTranslations.Construction.quadratic_cutoff_complete_square μ ψ q B hadd D (L y)
              (hshift (L y) (Or.inl ⟨y, hy, rfl⟩)), hvalue]
      rw [heq]
      ring
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero, mul_zero]

end

section

/-! Construction and transport of stable Gaussian cutoffs. -/

open _root_.MeasureTheory

theorem anisotropic_hasGaussianCutoffs
    {F V : Type} [NontriviallyNormedField F] [IsUltrametricDist F] [ProperSpace F]
    [NormedAddCommGroup V] [NormedSpace F V] [ProperSpace V] [MeasurableSpace V]
    (μ : Measure V) (ψ : AddChar F ℂ)
    (q : V → F) (hq : Continuous q) (hp : IsProperMap q)
    (B : V →L[F] V →L[F] F) (hadd : ∀ v x, q (v + x) = q v + q x + B v x)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ x, c * ‖x‖ ^ 2 ≤ ‖q x‖)
    (Γ : ℂ) (R₀ : ℝ)
    (hstable : ∀ r : ℝ, R₀ ≤ r →
      (∫ x, (q ⁻¹' Metric.closedBall 0 r).indicator (fun x => ψ (q x)) x ∂μ) = Γ) :
    HasGaussianCutoffs μ ψ q Γ := by
  intro K hK
  obtain ⟨M, -, hM⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨Q, -, hQ⟩ := (hK.image hq).isBounded.exists_pos_norm_le
  obtain ⟨R, hR, hshift⟩ := QuadraticCutoffTranslations.Construction.anisotropic_quadratic_cutoff_translation q hq B hadd c hc hlow M
  let r := max R (max R₀ Q)
  have hRr : R ≤ r := le_max_left _ _
  have hr : 0 < r := hR.trans_le hRr
  refine ⟨q ⁻¹' Metric.closedBall 0 r,
    hp.isCompact_preimage (isCompact_closedBall (0 : F) r),
    (IsUltrametricDist.isClopen_closedBall (0 : F) hr.ne').preimage hq, ?_, ?_, ?_⟩
  · intro x hx
    change q x ∈ Metric.closedBall (0 : F) r
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hQ (q x) ⟨x, hx, rfl⟩).trans ((le_max_right R₀ Q).trans (le_max_right _ _))
  · intro v hv x
    exact hshift r hRr v (hM v hv) x
  · exact hstable r ((le_max_left R₀ Q).trans (le_max_right _ _))

theorem HasGaussianCutoffs.transport
    {F V W : Type} [Field F] [AddCommGroup V] [AddCommGroup W]
    [TopologicalSpace V] [TopologicalSpace W] [T2Space V] [T2Space W]
    [MeasurableSpace V] [MeasurableSpace W] [BorelSpace V] [BorelSpace W]
    (e : V ≃ₜ+ W) (μ : Measure V) (ψ : AddChar F ℂ) (q : W → F) (Γ : ℂ)
    (hΓ : HasGaussianCutoffs (μ.map e) ψ q Γ) :
    HasGaussianCutoffs μ ψ (fun x => q (e x)) Γ := by
  intro K hK
  obtain ⟨D, hDc, hDo, hKD, hshift, hvalue⟩ := hΓ (e '' K) (hK.image e.continuous)
  refine ⟨e ⁻¹' D, e.toHomeomorph.isProperMap.isCompact_preimage hDc,
    hDo.preimage e.continuous, ?_, ?_, ?_⟩
  · intro x hx
    exact hKD ⟨x, hx, rfl⟩
  · intro v hv x
    change e (v + x) ∈ D ↔ e x ∈ D
    rw [map_add]
    exact hshift (e v) ⟨v, hv, rfl⟩ (e x)
  · have heq : (∫ x, D.indicator (fun x => ψ (q x)) x ∂μ.map e) =
        ∫ x, D.indicator (fun x => ψ (q x)) (e x) ∂μ :=
      e.toHomeomorph.isClosedEmbedding.integral_map
        (μ := μ) (f := D.indicator (fun x => ψ (q x)))
    rw [← hvalue, heq]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      by_cases hx : e x ∈ D
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ e ⁻¹' D from hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (show x ∉ e ⁻¹' D from hx)]

end

/-! Stable Gaussian cutoffs are preserved by finite orthogonal products. -/

open _root_.MeasureTheory
open scoped BigOperators

theorem addChar_sum_product {F ι : Type} [Field F] (ψ : AddChar F ℂ)
    (s : Finset ι) (f : ι → F) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, ψ.map_zero_eq_one]
  | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, ψ.map_add_eq_mul, ih]

theorem HasGaussianCutoffs.finite_product
    {F V ι : Type} [Field F] [AddCommGroup V] [TopologicalSpace V]
    [MeasurableSpace V] [Fintype ι]
    (μ : Measure V) [SigmaFinite μ] (ψ : AddChar F ℂ)
    (q : ι → V → F) (Γ : ι → ℂ) (hΓ : ∀ i, HasGaussianCutoffs μ ψ (q i) (Γ i)) :
    HasGaussianCutoffs (Measure.pi (fun _ : ι => μ)) ψ
      (fun x => ∑ i, q i (x i)) (∏ i, Γ i) := by
  classical
  intro K hK
  choose D hDc hDo hKD hshift hvalue using
    fun i : ι => hΓ i ((fun x : ι → V => x i) '' K) (hK.image (continuous_apply i))
  let T : Set (ι → V) := Set.univ.pi D
  have hTc : IsCompact T := isCompact_univ_pi hDc
  have hTo : IsClopen T := ⟨isClosed_set_pi (fun i _ => (hDo i).isClosed),
    isOpen_set_pi Set.finite_univ (fun i _ => (hDo i).isOpen)⟩
  refine ⟨T, hTc, hTo, ?_, ?_, ?_⟩
  · intro x hx i _
    exact hKD i ⟨x, hx, rfl⟩
  · intro v hv x
    change (∀ i ∈ Set.univ, v i + x i ∈ D i) ↔ ∀ i ∈ Set.univ, x i ∈ D i
    exact forall₂_congr fun i _ => hshift i (v i) ⟨v, hv, rfl⟩ (x i)
  · have heq (x : ι → V) : T.indicator (fun x => ψ (∑ i, q i (x i))) x =
        ∏ i, (D i).indicator (fun y => ψ (q i y)) (x i) := by
      by_cases hx : x ∈ T
      · rw [Set.indicator_of_mem hx]
        have hi (i : ι) : x i ∈ D i := hx i (Set.mem_univ i)
        simp_rw [Set.indicator_of_mem (hi _)]
        exact addChar_sum_product ψ Finset.univ (fun i => q i (x i))
      · rw [Set.indicator_of_notMem hx]
        have hex : ∃ i, x i ∉ D i := by
          by_contra hh
          push Not at hh
          exact hx (fun i _ => hh i)
        obtain ⟨i, hi⟩ := hex
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
    simp_rw [heq]
    rw [integral_fintype_prod_eq_prod (μ := fun _ : ι => μ)]
    exact Finset.prod_congr rfl (fun i _ => hvalue i)

end

end OAI.RepresentationTheory.Weil.UnitarySplitting.GaussianCutoff.Construction
