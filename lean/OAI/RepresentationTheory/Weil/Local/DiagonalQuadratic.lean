import OAI.RepresentationTheory.Weil.Local.GeneralGaussianCutoff
import OAI.RepresentationTheory.Weil.Local.FresnelLimit
import OAI.RepresentationTheory.Weil.Local.RealDiagonalFresnel

/-! # Diagonal Quadratic -/

namespace OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic.Construction

noncomputable section

section

/-! Tensor cutoffs for arbitrary nonsingular diagonal quadratic phases. -/

open _root_.Matrix _root_.MeasureTheory

def diagonalCompactQuadratic {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (a : Fin n → kˣ) (W : Fin n → Set k) (x : FunctionsMetaplectic.Construction.Position k n) : ℂ :=
  ∏ i, QuadraticFourier.Construction.compactQuadraticFunction ψ (W i) (a i).val (x i)

theorem diagonalCompactQuadratic_on {k : Type} [Field k] {n : ℕ}
    (ψ : AddChar k ℂ) (a : Fin n → kˣ) (W : Fin n → Set k)
    (x : FunctionsMetaplectic.Construction.Position k n) (hx : ∀ i, x i ∈ W i) :
    diagonalCompactQuadratic ψ a W x = ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x) := by
  simp only [diagonalCompactQuadratic, QuadraticFourier.Construction.compactQuadraticFunction, Set.indicator_of_mem (hx _)]
  rw [RealDiagonalFresnel.Construction.quadratic_diagonal, CompactCharacter.Construction.character_finset_sum]

theorem diagonalCompactQuadratic_compactSupport {k : Type} [NormedField k] {n : ℕ}
    (ψ : AddChar k ℂ) (a : Fin n → kˣ) (W : Fin n → Set k) (hW : ∀ i, IsCompact (W i)) :
    HasCompactSupport (diagonalCompactQuadratic ψ a W) := by
  apply HasCompactSupport.intro (isCompact_pi_infinite hW)
  intro x hx
  change ¬ ∀ i, x i ∈ W i at hx
  obtain ⟨i, hi⟩ := not_forall.mp hx
  exact Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)

theorem diagonalCompactQuadratic_locallyConstant
    {k : Type} [NormedField k] [NonarchimedeanAddGroup k] {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (a : Fin n → kˣ) (W : Fin n → OpenAddSubgroup k) :
    IsLocallyConstant (diagonalCompactQuadratic ψ a (fun i => W i)) := by
  have hprod (s : Finset (Fin n)) : IsLocallyConstant
      (fun x : FunctionsMetaplectic.Construction.Position k n => ∏ i ∈ s, QuadraticFourier.Construction.compactQuadraticFunction ψ (W i) (a i).val (x i)) := by
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.prod_empty, Function.const_def] using! (IsLocallyConstant.const (1 : ℂ))
    | @insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact ((GaussianCompact.Construction.compactQuadratic_locallyConstant ψ hu hc (W i) (a i).val).comp_continuous
        (continuous_apply i)).mul ih
  exact hprod Finset.univ

theorem scalarFourier_compactQuadratic_div
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (a : kˣ) (W : OpenAddSubgroup k) (x : k) (hx : x / a.val ∈ W) :
    FourierTensor.Construction.scalarFourierIntegral ψ μ (QuadraticFourier.Construction.compactQuadraticFunction ψ W a.val) x =
      ψ (-(a.val⁻¹ * x ^ 2 / 2)) * ∫ y in (W : Set k), ψ (a.val * y ^ 2 / 2) ∂μ := by
  have h := QuadraticFourier.Construction.scalarFourier_compactQuadratic ψ μ W a.val (x / a.val) hx
  have hi : a.val * (x / a.val) = x := by field_simp
  have hq : a.val * (x / a.val) ^ 2 / 2 = a.val⁻¹ * x ^ 2 / 2 := by field_simp
  rwa [hi, hq] at h

theorem fourier_diagonalCompactQuadratic_on
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure] [SigmaFinite μ]
    (a : Fin n → kˣ) (W : Fin n → OpenAddSubgroup k)
    (x : FunctionsMetaplectic.Construction.Position k n) (hx : ∀ i, x i / (a i).val ∈ W i) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ))
      (diagonalCompactQuadratic ψ a (fun i => W i)) x =
      (∏ i, ∫ y in (W i : Set k), ψ ((a i).val * y ^ 2 / 2) ∂μ) *
        ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) := by
  unfold diagonalCompactQuadratic
  rw [FourierTensor.Construction.fourierIntegral_product]
  simp_rw [scalarFourier_compactQuadratic_div ψ μ (a _) (W _) _ (hx _)]
  rw [Finset.prod_mul_distrib, RealDiagonalFresnel.Construction.quadratic_diagonal, ← Finset.sum_neg_distrib,
    CompactCharacter.Construction.character_finset_sum, mul_comm]

end

section

/-! The exact nonarchimedean Fresnel pairing for every nonsingular diagonal form. -/

open _root_.Matrix _root_.MeasureTheory

def diagonalGaussianCoefficient {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] {n : ℕ} (ψ : AddChar k ℂ) (a : Fin n → kˣ) : ℂ :=
  ∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val * ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (a i)))⁻¹ : ℂ)

theorem nonarchimedean_diagonal_fresnel_pairing
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : Fin n → kˣ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x *
      ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
      diagonalGaussianCoefficient ψ a *
        ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x)
          ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
  let μn := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μn.IsAddHaarMeasure := by dsimp [μn, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  obtain ⟨hf, hs⟩ := NonarchimedeanTestSpace.Construction.schwartzBruhat_totallyDisconnected_iff.mp f.property
  have hFs := CompactCharacter.Construction.fourierIntegral_compactSupport_of_locallyConstant hNondiscrete ψ hn μn hf hs
  let K (i : Fin n) : Set k :=
    (fun x : FunctionsMetaplectic.Construction.Position k n => x i / (a i).val) '' tsupport f.val ∪
      (fun x : FunctionsMetaplectic.Construction.Position k n => x i) '' tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val)
  have hK (i : Fin n) : IsCompact (K i) :=
    (hs.image ((continuous_apply i).div_const _)).union (hFs.image (continuous_apply i))
  choose W hW hKW hG using fun i => GeneralGaussianCutoff.Construction.exists_gaussian_coefficient_cutoff hNondiscrete ψ hu hc hn (a i) (K i) (hK i)
  let g := diagonalCompactQuadratic ψ a (fun i => W i)
  have hgi : Integrable g μn :=
    (diagonalCompactQuadratic_locallyConstant ψ hu hc a W).continuous.integrable_of_hasCompactSupport
      (diagonalCompactQuadratic_compactSupport ψ a (fun i => W i) hW)
  have hxWF (x : FunctionsMetaplectic.Construction.Position k n) (hx : x ∈ tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val)) :
      ∀ i, x i ∈ W i := fun i => hKW i (Or.inr ⟨x, hx, rfl⟩)
  have hxWf (x : FunctionsMetaplectic.Construction.Position k n) (hx : x ∈ tsupport f.val) :
      ∀ i, x i / (a i).val ∈ W i := fun i => hKW i (Or.inl ⟨x, hx, rfl⟩)
  calc
    _ = ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val x * g x ∂μn := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val x * ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x) =
          FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val x * g x
        by_cases hx : x ∈ tsupport (FunctionsMetaplectic.Construction.fourierIntegral ψ μn f.val)
        · change _ = _ * diagonalCompactQuadratic ψ a (fun i => W i) x
          rw [diagonalCompactQuadratic_on ψ a (fun i => W i) x (hxWF x hx)]
        · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
    _ = ∫ x, f.val x * FunctionsMetaplectic.Construction.fourierIntegral ψ μn g x ∂μn :=
      FresnelLimit.Construction.fourierIntegral_mul_swap ψ hu hc μn (hf.continuous.integrable_of_hasCompactSupport hs) hgi
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change f.val x * FunctionsMetaplectic.Construction.fourierIntegral ψ μn g x = diagonalGaussianCoefficient ψ a *
          (f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x))
        by_cases hx : x ∈ tsupport f.val
        · change f.val x * FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ))
            (diagonalCompactQuadratic ψ a (fun i => W i)) x = _
          rw [fourier_diagonalCompactQuadratic_on ψ μ a W x (hxWf x hx)]
          change f.val x * ((∏ i, ∫ y in (W i : Set k), ψ ((a i).val * y ^ 2 / 2)
            ∂ FunctionsMetaplectic.Construction.selfDualMeasure k ψ) * _) = _
          simp_rw [hG]
          change _ = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val * ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (a i)))⁻¹ : ℂ)) * _
          ring
        · rw [image_eq_zero_of_notMem_tsupport hx]
          ring

end

/-! A concrete compact test function detects every quadratic Fresnel coefficient. -/

open _root_.MeasureTheory _root_.Matrix

theorem exists_nonarchimedean_quadratic_pairing_ne_zero
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (B : Matrix (Fin n) (Fin n) k) :
    ∃ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, (∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic B x) ∂μ) ≠ 0 := by
  let : IsUltrametricDist k := NonarchimedeanNorm.Construction.nonarchimedean_norm_ultrametric k hnd
  let : ProperSpace k := FunctionsMetaplectic.Construction.localField_proper k hnd
  let U := IsUltrametricDist.closedBall_openAddSubgroup (FunctionsMetaplectic.Construction.Position k n) zero_lt_one
  have hU : IsCompact (U : Set (FunctionsMetaplectic.Construction.Position k n)) := isCompact_closedBall 0 1
  let b : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨(U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => 1),
    FunctionsMetaplectic.Construction.compact_locallyConstant_mem (CompactCharacter.Construction.subgroup_indicator_locallyConstant U)
      (CompactCharacter.Construction.subgroup_indicator_compactSupport U hU)⟩
  let f : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨FunctionsMetaplectic.Construction.quadraticOperator ψ B b.val, NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc B b⟩
  have he : (fun x => f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic B x)) =
      (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) := by
    funext x
    change (ψ (FunctionsMetaplectic.Construction.quadratic B x) * (U : Set (FunctionsMetaplectic.Construction.Position k n)).indicator (fun _ => (1 : ℂ)) x) *
      ψ (-FunctionsMetaplectic.Construction.quadratic B x) = _
    by_cases hx : x ∈ U
    · rw [Set.indicator_of_mem hx, mul_one, ← ψ.map_add_eq_mul, add_neg_cancel, ψ.map_zero_eq_one]
    · rw [Set.indicator_of_notMem hx, mul_zero, zero_mul]
  refine ⟨f, ?_⟩
  rw [he, integral_indicator_const _ U.isOpen.measurableSet, Complex.real_smul, mul_one]
  apply Complex.ofReal_ne_zero.mpr
  apply (ENNReal.toReal_pos _ hU.measure_ne_top).ne'
  exact (Measure.measure_pos_of_nonempty_interior μ
    (by rw [U.isOpen.interior_eq]; exact ⟨0, U.zero_mem⟩)).ne'

end

end OAI.RepresentationTheory.Weil.Local.DiagonalQuadratic.Construction
