import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.SingleLineSourceFamily
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteLineLagrangianPair
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.HeckeCycles
import OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity

/-! # Concrete Source Families -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSourceFamilies.CM

noncomputable section

section

/-! The original two lines and the actual approximating two lines give
four full source families on one principal surface family. Their finite
inputs are fixed across every eligible level. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]

omit [IsGalois ℚ K] in
theorem source_family_at_multiple (d : Gal(K/ℚ) → Bool) (M L : ℕ) (hML : M ∣ L)
    (X : ℕ → Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((X N).rationalCohomology 1))
    (hsource : HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K d M X Θ) : HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K d L X Θ := by
  obtain ⟨B, places, P, φ, hlevels⟩ := hsource
  exact ⟨B, places, P, φ, fun N hN hLN => hlevels N hN (hML.trans hLN)⟩

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)

def actualFourThetaSigns : Fin 2 ⊕ Fin 2 → Gal(K/ℚ) → Bool :=
  Sum.elim (FourSplittings.CM.initialThetaSigns K v) (FourSplittings.CM.newThetaSigns K v)

def actualFourLinePeriods : (i : Fin 2 ⊕ Fin 2) →
    HeckeCycles.GeometricSource.CM.LinePeriod K D.ball D.places (actualFourThetaSigns K (v := v) i)
  | .inl j => D.initialPeriods j
  | .inr j => A.periods j

include hid

theorem exists_actual_four_source_families
    (Φ : Fin 2 ⊕ Fin 2 → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places)) :
    ∃ (M : ℕ) (_hM : 0 < M) (hDM : D.depth ∣ M)
      (Θ : (Fin 2 ⊕ Fin 2) → ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
      ∀ i, HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (actualFourThetaSigns K (v := v) i) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) ∧
        SingleLineSourceFamily.CM.SetupSourceRepresentatives K D (actualFourLinePeriods K D A i) (Φ i) M hDM (Θ i) := by
  have hQ := ConcreteLineLagrangianPair.CM.exists_actual_approximation_lagrangian_pair K D A hid
  have hsingle (i : Fin 2 ⊕ Fin 2) :
      ∃ (M : ℕ) (_hM : 0 < M) (hDM : D.depth ∣ M)
        (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
        HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (actualFourThetaSigns K (v := v) i) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) Θ ∧
          SingleLineSourceFamily.CM.SetupSourceRepresentatives K D (actualFourLinePeriods K D A i) (Φ i) M hDM Θ := by
    cases i with
    | inl j =>
      exact SingleLineSourceFamily.CM.exists_setup_single_source_family K D (FourSplittings.CM.initialThetaSigns K v) D.pair
        (ConcreteApproximationIntrinsicArithmetic.CM.initial_native_active_signs K D hid) j (D.initialPeriods j) (D.initial_coefficients j) (Φ (.inl j))
    | inr j =>
      exact SingleLineSourceFamily.CM.exists_setup_single_source_family K D (FourSplittings.CM.newThetaSigns K v) hQ.choose
        (ConcreteApproximationIntrinsicArithmetic.CM.approximation_native_active_signs K D hid) j (A.periods j) (hQ.choose_spec.2.2 j) (Φ (.inr j))
  choose m hm hDm Θ hsource hrep using hsingle
  let M := D.depth * ∏ i, m i
  have hM : 0 < M := Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 3) D.depth_ge_three)
    (Finset.prod_pos (fun i _ => hm i))
  refine ⟨M, hM, dvd_mul_right _ _, Θ, ?_⟩
  intro i
  have hi : m i ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) D.depth
  refine ⟨source_family_at_multiple K _ (m i) M hi (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) (hsource i), ?_⟩
  intro N hN hMN
  exact hrep i N hN (hi.trans hMN)

omit D A hid [IsGalois ℚ K] in
theorem actual_four_theta_signs_eq (i : Fin 2 ⊕ Fin 2) (τ : Gal(K/ℚ)) :
    actualFourThetaSigns K (v := v) i τ = (v (finSumFinEquiv i)).val τ⁻¹ := by
  cases i with
  | inl j => fin_cases j <;> rfl
  | inr j => fin_cases j <;> rfl

theorem exists_actual_four_cm_source_families (hHeckeCycles : HeckeCycles.CM.HeckeCyclesInput)
    (Φ : Fin 2 ⊕ Fin 2 → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places)) :
    ∃ (M : ℕ) (_hM : 3 ≤ M) (hDM : D.depth ∣ M)
      (Θ : (Fin 2 ⊕ Fin 2) → ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
      (∀ i, HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (actualFourThetaSigns K (v := v) i) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) ∧
        SingleLineSourceFamily.CM.SetupSourceRepresentatives K D (actualFourLinePeriods K D A i) (Φ i) M hDM (Θ i)) ∧
      ∀ N : ℕ, 0 < N → M ∣ N → ∀ i,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).toOver) 1 (Θ i N) ∈
          Cm.cmLineSpan K (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) (SetupSurfaceFamily.CM.setupSurfaceHodge K D N) (v (finSumFinEquiv i)) 1 ∧
        ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).toOver) 1 (Θ i N)) ∈
            Cm.cmLineSpan K (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) (SetupSurfaceFamily.CM.setupSurfaceHodge K D N)
              (v (finSumFinEquiv i)) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) := by
  obtain ⟨L, hL, hDL, Θ, hsource⟩ := exists_actual_four_source_families K D A hid Φ
  have hs (i : Fin 2 ⊕ Fin 2) : HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K
      (fun τ => (v (finSumFinEquiv i)).val τ⁻¹) L (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) := by
    have he := funext (actual_four_theta_signs_eq K (v := v) i)
    rw [← he]
    exact (hsource i).1
  have h := HeckeCycles.CM.p41_finite_family_common_level hHeckeCycles K (fun i : Fin 2 ⊕ Fin 2 => v (finSumFinEquiv i))
    (fun i => hid (finSumFinEquiv i)) L hL (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (SetupSurfaceFamily.CM.setupSurfaceHodge K D)
    (SetupSurfaceFamily.CM.setup_surface_hodge_canonical K D) Θ hs
  refine ⟨h.choose, h.choose_spec.1, hDL.trans h.choose_spec.2.1, Θ, ?_, h.choose_spec.2.2⟩
  intro i
  refine ⟨source_family_at_multiple K _ L h.choose h.choose_spec.2.1 _ _ (hsource i).1, ?_⟩
  intro N hN hMN
  exact (hsource i).2 N hN (h.choose_spec.2.1.trans hMN)

end

section

/-! Every finite collection of actual source inputs in the four specified
sign families has one common principal level. Apply full HeckeCycles while keeping
each fixed input and its actual canonical-surface representatives. -/

open scoped Classical BigOperators
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]
  {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)
  {J : Type} [Fintype J] (σ : J → Fin 2 ⊕ Fin 2)
  (Φ : J → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places))

include hid in
theorem exists_actual_indexed_source_families :
    ∃ (M : ℕ) (_hM : 0 < M) (hDM : D.depth ∣ M)
      (Θ : J → ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
      ∀ i, HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (actualFourThetaSigns K (v := v) (σ i)) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) ∧
        SingleLineSourceFamily.CM.SetupSourceRepresentatives K D (actualFourLinePeriods K D A (σ i)) (Φ i) M hDM (Θ i) := by
  have hsingle (i : J) :
      ∃ (M : ℕ) (_hM : 0 < M) (hDM : D.depth ∣ M)
        (Θ : ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
        HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (actualFourThetaSigns K (v := v) (σ i)) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) Θ ∧
          SingleLineSourceFamily.CM.SetupSourceRepresentatives K D (actualFourLinePeriods K D A (σ i)) (Φ i) M hDM Θ := by
    obtain ⟨M, hM, hDM, Θ, hΘ⟩ := exists_actual_four_source_families K D A hid (fun _ => Φ i)
    exact ⟨M, hM, hDM, Θ (σ i), hΘ (σ i)⟩
  choose m hm hDm Θ hsource hrep using hsingle
  let M := D.depth * ∏ i, m i
  have hM : 0 < M := Nat.mul_pos (lt_of_lt_of_le (by decide : 0 < 3) D.depth_ge_three)
    (Finset.prod_pos (fun i _ => hm i))
  refine ⟨M, hM, dvd_mul_right _ _, Θ, ?_⟩
  intro i
  have hi : m i ∣ M := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem m (Finset.mem_univ i)) D.depth
  refine ⟨source_family_at_multiple K _ (m i) M hi _ _ (hsource i), ?_⟩
  intro N hN hMN
  exact hrep i N hN (hi.trans hMN)

include hid in
theorem exists_actual_indexed_cm_source_families (hHeckeCycles : HeckeCycles.CM.HeckeCyclesInput) :
    ∃ (M : ℕ) (_hM : 3 ≤ M) (hDM : D.depth ∣ M)
      (Θ : J → ∀ N, ComplexMultiplication.WeightOne.CM.Complexification ((SetupSurfaceFamily.CM.setupSurfaceFamily K D N).rationalCohomology 1)),
      (∀ i, HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K (actualFourThetaSigns K (v := v) (σ i)) M (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) ∧
        SingleLineSourceFamily.CM.SetupSourceRepresentatives K D (actualFourLinePeriods K D A (σ i)) (Φ i) M hDM (Θ i)) ∧
      ∀ N : ℕ, 0 < N → M ∣ N → ∀ i,
        ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).toOver) 1 (Θ i N) ∈
          Cm.cmLineSpan K (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) (SetupSurfaceFamily.CM.setupSurfaceHodge K D N) (v (finSumFinEquiv (σ i))) 1 ∧
        ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
          (ComplexMultiplication.CohomologyBaseChange.CM.singularCohomologyComplexification (Betti.Scheme.schemePointSpace (SetupSurfaceFamily.CM.setupSurfaceFamily K D N).toOver) 1 (Θ i N)) ∈
            Cm.cmLineSpan K (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) (SetupSurfaceFamily.CM.setupSurfaceHodge K D N)
              (v (finSumFinEquiv (σ i))) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) := by
  obtain ⟨L, hL, hDL, Θ, hsource⟩ := exists_actual_indexed_source_families K D A hid σ Φ
  have hs (i : J) : HeckeCycles.GeometricSource.CM.IsSourceBallThetaFamily K
      (fun τ => (v (finSumFinEquiv (σ i))).val τ⁻¹) L (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (Θ i) := by
    have he := funext (actual_four_theta_signs_eq K (v := v) (σ i))
    rw [← he]
    exact (hsource i).1
  have h := HeckeCycles.CM.p41_finite_family_common_level hHeckeCycles K (fun i : J => v (finSumFinEquiv (σ i)))
    (fun i => hid (finSumFinEquiv (σ i))) L hL (SetupSurfaceFamily.CM.setupSurfaceFamily K D) (SetupSurfaceFamily.CM.setupSurfaceHodge K D)
    (SetupSurfaceFamily.CM.setup_surface_hodge_canonical K D) Θ hs
  refine ⟨h.choose, h.choose_spec.1, hDL.trans h.choose_spec.2.1, Θ, ?_, h.choose_spec.2.2⟩
  intro i
  refine ⟨source_family_at_multiple K _ L h.choose h.choose_spec.2.1 _ _ (hsource i).1, ?_⟩
  intro N hN hMN
  exact (hsource i).2 N hN (h.choose_spec.2.1.trans hMN)

end

/-! Full HeckeCycles supplies actual source one-forms on every sufficiently deep
principal surface, with the canonical Hodge structure and both embedding labels. -/

open scoped Classical
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K] [IsGalois ℚ K]

theorem source_cm_form_transport {B : HeckeCycles.GeometricSource.CM.BallDatum K} {N : ℕ}
    {X Y : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} (h : X = Y)
    (π : B.Domain → Y.analyticSpace) (hπ : B.IsBallCover N Y π)
    (w : ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g))
    (ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms X.analyticModel X.analyticSpace 1 0)
    (hid : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 ω.val ∈ Cm.cmLineSpan K X (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 X) w 1)
    (hc : ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 X (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass X 1 ω.val) ∈
      Cm.cmLineSpan K X (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 X) w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K)) :
    ∃ η : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms Y.analyticModel Y.analyticSpace 1 0,
      CoverPullback.CM.ballCoverPullback K B N Y π hπ 1 η.val.val =
        CoverPullback.CM.ballCoverPullback K B N X (h.symm ▸ π) (SetupSurfaceFamily.CM.source_cover_transport K h π hπ) 1 ω.val.val ∧
      AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass Y 1 η.val ∈ Cm.cmLineSpan K Y (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 Y) w 1 ∧
      ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 Y (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass Y 1 η.val) ∈
        Cm.cmLineSpan K Y (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 Y) w (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) := by
  cases h
  exact ⟨ω, rfl, hid, hc⟩

variable {v : Fin 4 → ComplexMultiplication.OddSignSwitch.CM.OddSignPattern (fun g : Gal(K/ℚ) => ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K * g)} {Nbase : ℕ}
  (D : PeriodTotal.CM.FourPeriodSetup K v Nbase) {ε : ℝ}
  (A : PeriodTotal.CM.RationalPeriodApproximation K v D.ball D.places D.pair ε)
  (hid : ∀ i, (v i).val 1 = true)
  {J : Type} [Fintype J] (σ : J → Fin 2 ⊕ Fin 2)
  (Φ : J → HeckeCycles.GeometricSource.CM.FiniteInput (HeckeCycles.GeometricSource.CM.Positions K D.places))

include hid in
theorem exists_actual_principal_source_classes (hHeckeCycles : HeckeCycles.CM.HeckeCyclesInput) :
    ∃ (M : ℕ) (_hM : 3 ≤ M) (hDM : D.depth ∣ M),
      ∀ (N : ℕ) (hN : 0 < N) (hMN : M ∣ N),
        let S := D.surface N hN (hDM.trans hMN)
        ∀ i, ∃ ω : AlgebraicTopology.DeRham.Comparison.ManifoldPureClasses.pureClosedManifoldForms
          S.surface.variety.analyticModel S.surface.variety.analyticSpace 1 0,
          CoverPullback.CM.ballCoverPullback K D.ball N S.surface.variety S.projection S.isBallCover 1 ω.val.val =
            BallForms.CM.sourceBallOneForm K (actualFourLinePeriods K D A (σ i)) (Φ i) ∧
          AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 1 ω.val ∈ Cm.cmLineSpan K S.surface.variety
            (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.surface.variety) (v (finSumFinEquiv (σ i))) 1 ∧
          ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 S.surface.variety (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass S.surface.variety 1 ω.val) ∈
            Cm.cmLineSpan K S.surface.variety (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 S.surface.variety)
              (v (finSumFinEquiv (σ i))) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) := by
  obtain ⟨M, hM, hDM, Θ, hsource, hCM⟩ :=
    exists_actual_indexed_cm_source_families K D A hid σ Φ hHeckeCycles
  refine ⟨M, hM, hDM, ?_⟩
  intro N hN hMN
  dsimp only
  intro i
  obtain ⟨ω, hω, _, hclass⟩ := (hsource i).2 N hN hMN
  change _ = AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) 1 ω.val at hclass
  have hidω : AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) 1 ω.val ∈
      Cm.cmLineSpan K (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 (SetupSurfaceFamily.CM.setupSurfaceFamily K D N))
        (v (finSumFinEquiv (σ i))) 1 := by
    rw [← hclass]
    exact (hCM N hN hMN i).1
  have hcω : ComplexMultiplication.HodgeComparison.BettiConjugation.CM.Construction.conjugateBettiH1 (SetupSurfaceFamily.CM.setupSurfaceFamily K D N)
      (AlgebraicTopology.Kunneth.ProjectiveCupPurity.Constructions.projectiveFormBettiClass (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) 1 ω.val) ∈
      Cm.cmLineSpan K (SetupSurfaceFamily.CM.setupSurfaceFamily K D N) (Albanese.HodgeComparisonIs.CM.Construction.canonicalH1 (SetupSurfaceFamily.CM.setupSurfaceFamily K D N))
        (v (finSumFinEquiv (σ i))) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation K) := by
    rw [← hclass]
    exact (hCM N hN hMN i).2
  obtain ⟨η, hη, hηid, hηc⟩ := source_cm_form_transport K
    (SetupSurfaceFamily.CM.setup_surface_family_eq K D N hN (hDM.trans hMN))
    (D.surface N hN (hDM.trans hMN)).projection (D.surface N hN (hDM.trans hMN)).isBallCover
    (v (finSumFinEquiv (σ i))) ω hidω hcω
  exact ⟨η, hη.trans hω, hηid, hηc⟩

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.ConcreteSourceFamilies.CM
