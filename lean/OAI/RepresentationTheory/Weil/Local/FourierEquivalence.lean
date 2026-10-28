import OAI.RepresentationTheory.Weil.Local.RealFourierLp
import OAI.RepresentationTheory.Weil.Local.QuadraticIntertwiner

/-! # Fourier Equivalence -/

namespace OAI.RepresentationTheory.Weil.Local.FourierEquivalence.Construction

noncomputable section

section

/-! Fourier covariance with the Heisenberg action, and the real oscillator lift. -/

open _root_.MeasureTheory
open scoped BigOperators

theorem positionPart_weyl {k : Type} [Field k] {n : ℕ} (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    LinearIntertwiner.Construction.positionPart (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v) = LinearIntertwiner.Construction.momentumPart v := by
  funext i
  simp [LinearIntertwiner.Construction.positionPart, LinearIntertwiner.Construction.momentumPart, FunctionsMetaplectic.Construction.symplecticAction, Generators.Construction.weylSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem momentumPart_weyl {k : Type} [Field k] {n : ℕ} (v : FunctionsMetaplectic.Construction.PhaseSpace k n) :
    LinearIntertwiner.Construction.momentumPart (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v) = -LinearIntertwiner.Construction.positionPart v := by
  funext i
  simp [LinearIntertwiner.Construction.positionPart, LinearIntertwiner.Construction.momentumPart, FunctionsMetaplectic.Construction.symplecticAction, Generators.Construction.weylSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem fourierIntegral_heisenberg
    {k : Type} [NormedField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      FunctionsMetaplectic.Construction.heisenbergFunction ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  funext x
  rw [LinearIntertwiner.Construction.heisenbergFunction_eq_dot, positionPart_weyl, momentumPart_weyl]
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_add_right_eq_self
    (fun y => FunctionsMetaplectic.Construction.heisenbergFunction ψ v f y * ψ (-FunctionsMetaplectic.Construction.dot x y)) (LinearIntertwiner.Construction.positionPart v)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [LinearIntertwiner.Construction.heisenbergFunction_eq_dot, add_sub_cancel_right]
    have hphase :
        FunctionsMetaplectic.Construction.dot (LinearIntertwiner.Construction.momentumPart v) (y + LinearIntertwiner.Construction.positionPart v - (2 : k)⁻¹ • LinearIntertwiner.Construction.positionPart v) -
          FunctionsMetaplectic.Construction.dot x (y + LinearIntertwiner.Construction.positionPart v) =
        FunctionsMetaplectic.Construction.dot (-LinearIntertwiner.Construction.positionPart v) (x - (2 : k)⁻¹ • LinearIntertwiner.Construction.momentumPart v) -
          FunctionsMetaplectic.Construction.dot (x - LinearIntertwiner.Construction.momentumPart v) y := by
      simp only [FunctionsMetaplectic.Construction.dot, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      _ = ψ (FunctionsMetaplectic.Construction.dot (LinearIntertwiner.Construction.momentumPart v)
          (y + LinearIntertwiner.Construction.positionPart v - (2 : k)⁻¹ • LinearIntertwiner.Construction.positionPart v) - FunctionsMetaplectic.Construction.dot x (y + LinearIntertwiner.Construction.positionPart v)) * f y := by
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring
      _ = _ := by
        rw [hphase]
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring

theorem real_heisenberg_mem {n : ℕ} (c : ℝ) (v : FunctionsMetaplectic.Construction.PhaseSpace ℝ n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    FunctionsMetaplectic.Construction.heisenbergFunction (Gaussian.Construction.realCharacter c) v f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℝ n := by
  let φ := (RealTestSpace.Construction.realSchwartzEquiv n).symm f
  let p : FunctionsMetaplectic.Construction.Position ℝ n → ℝ := fun x => ∑ i, v (Sum.inr i) * (x i - v (Sum.inl i) / 2)
  have hp : Function.HasTemperateGrowth p := by
    exact .sum (fun i _ => (Function.HasTemperateGrowth.const _).mul
      ((ContinuousLinearMap.proj i : FunctionsMetaplectic.Construction.Position ℝ n →L[ℝ] ℝ).hasTemperateGrowth.sub (.const _)))
  let χ := SchwartzMap.smulLeftCLM ℂ (fun x => Gaussian.Construction.realCharacter c (p x))
    (φ.compSubConstCLM ℂ (LinearIntertwiner.Construction.positionPart v))
  refine RealTestSpace.Construction.schwartzBruhat_real_iff.mpr ⟨χ, ?_⟩
  funext x
  change _ = (SchwartzMap.smulLeftCLM ℂ (Gaussian.Construction.realCharacter c ∘ p)
    (φ.compSubConstCLM ℂ (LinearIntertwiner.Construction.positionPart v))) x
  rw [SchwartzMap.smulLeftCLM_apply_apply ((RealTestSpace.Construction.realCharacter_temperate c).comp hp)]
  change _ = Gaussian.Construction.realCharacter c (p x) * φ (x - LinearIntertwiner.Construction.positionPart v)
  rw [RealTestSpace.Construction.realSchwartzEquiv_symm_apply]
  rfl

theorem realBruhatFourier_intertwines {n : ℕ}
    (v : FunctionsMetaplectic.Construction.PhaseSpace ℝ n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    FunctionsMetaplectic.Construction.heisenbergGraph (Gaussian.Construction.realCharacter 1) v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic ℝ n) v)
        (RealFourierLp.Construction.realBruhatFourier n f) (RealFourierLp.Construction.realBruhatFourier n h) := by
  let hf : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n :=
    ⟨FunctionsMetaplectic.Construction.heisenbergFunction (Gaussian.Construction.realCharacter 1) v f.val, real_heisenberg_mem 1 v f⟩
  have hcov : (RealFourierLp.Construction.realBruhatFourier n hf).val =
      FunctionsMetaplectic.Construction.heisenbergFunction (Gaussian.Construction.realCharacter 1) (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic ℝ n) v)
        (RealFourierLp.Construction.realBruhatFourier n f).val := by
    have heq (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
        (RealFourierLp.Construction.realBruhatFourier n g).val = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume g.val :=
      funext (RealFourierLp.Construction.realBruhatFourier_apply g)
    rw [heq, heq]
    exact fourierIntegral_heisenberg (Gaussian.Construction.realCharacter 1) volume v f.val
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [← hcov]
  change h.val = hf.val ↔ (RealFourierLp.Construction.realBruhatFourier n h).val = (RealFourierLp.Construction.realBruhatFourier n hf).val
  constructor
  · intro hh
    rw [Subtype.ext hh]
  · intro hh
    exact congrArg Subtype.val ((RealFourierLp.Construction.realBruhatFourier n).injective (Subtype.ext hh))

theorem realBruhatFourier_unitary {n : ℕ} (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    FunctionsMetaplectic.Construction.l2Energy ℝ n (RealFourierLp.Construction.realBruhatFourier n f) = FunctionsMetaplectic.Construction.l2Energy ℝ n f := by
  let μ : Measure (FunctionsMetaplectic.Construction.Position ℝ n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure ℝ))
  have h := Measure.isAddLeftInvariant_eq_smul_of_regular μ volume
  change (∫ x, ‖(RealFourierLp.Construction.realBruhatFourier n f).val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ
  rw [h, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  congr 1
  simp_rw [RealFourierLp.Construction.realBruhatFourier_apply]
  exact RealFourierLp.Construction.real_fourier_plancherel_standard f

/-- The Fourier operator has been constructed and verified in the oscillator extension.
The Gaussian phase selecting a bare-cover lift is a further statement. -/
def realFourierOscillator (n : ℕ) : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter 1) :=
  ⟨(Generators.Construction.weylSymplectic ℝ n, RealFourierLp.Construction.realBruhatFourier n),
    ⟨realBruhatFourier_unitary, realBruhatFourier_intertwines⟩⟩

theorem realFourierOscillator_apply {n : ℕ}
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    ((realFourierOscillator n).val.2 f).val x = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val x :=
  RealFourierLp.Construction.realBruhatFourier_apply f x

end

/-! Constructing a Fourier oscillator from proved stability and inversion. -/

open _root_.MeasureTheory
open scoped BigOperators

theorem heisenbergFunction_weyl_twice_reflect
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.heisenbergFunction ψ
      (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v))
      (fun y => f (-y)) (-x) = FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x := by
  rw [LinearIntertwiner.Construction.heisenbergFunction_eq_dot, LinearIntertwiner.Construction.heisenbergFunction_eq_dot,
    positionPart_weyl, momentumPart_weyl, positionPart_weyl, momentumPart_weyl]
  congr 2
  · simp only [FunctionsMetaplectic.Construction.dot, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · funext i
    simp [sub_eq_add_neg, add_comm]

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
  (hStable : ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n, FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ FunctionsMetaplectic.Construction.schwartzBruhat k n)
  (hInv : ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = f.val (-x))

def testFourierLinear : FunctionsMetaplectic.Construction.schwartzBruhat k n →ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  (FourierTools.Construction.schwartzBruhat_fourierLinearMap n ψ hu hc μ).codRestrict _ hStable

include hInv

omit [LocallyCompactSpace k] in
theorem testFourierLinear_square (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    (testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable f)).val x =
      f.val (-x) := hInv f x

omit [LocallyCompactSpace k] in
theorem testFourierLinear_fourth (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable
      (testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable f))) = f := by
  apply Subtype.ext
  funext x
  rw [testFourierLinear_square ψ hu hc μ hStable hInv,
    testFourierLinear_square ψ hu hc μ hStable hInv, neg_neg]

def testFourier : FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat k n where
  toLinearMap := testFourierLinear ψ hu hc μ hStable
  invFun f := testFourierLinear ψ hu hc μ hStable
    (testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable f))
  left_inv := testFourierLinear_fourth ψ hu hc μ hStable hInv
  right_inv := testFourierLinear_fourth ψ hu hc μ hStable hInv

omit [LocallyCompactSpace k] in
theorem testFourier_apply (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (testFourier ψ hu hc μ hStable hInv f).val = FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val := rfl

include hu hc hStable in
theorem fourierIntegral_norm_sq (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, ‖FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ := by
  have hf := FunctionsMetaplectic.Construction.schwartzBruhat_integrable μ f
  have hg := FunctionsMetaplectic.Construction.schwartzBruhat_integrable μ (testFourierLinear ψ hu hc μ hStable f)
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (innerSL ℂ) (L := dotProductBilin k k)
    (FourierTools.Construction.circleCharacter_continuous ψ hu hc) (FourierTools.Construction.dotProductBilin_continuous n) hf hg
  have hneg (x : FunctionsMetaplectic.Construction.Position k n) :
      VectorFourier.fourierIntegral (FourierTools.Construction.circleCharacter ψ hu) μ
        (-(dotProductBilin k k).flip) (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = f.val x := by
    have hi := hInv f (-x)
    rw [neg_neg] at hi
    rw [← hi]
    unfold VectorFourier.fourierIntegral FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [LinearMap.neg_apply, LinearMap.flip_apply,
        Circle.smul_def, smul_eq_mul]
      change ψ (- -FunctionsMetaplectic.Construction.dot x y) * _ = _ * ψ (-FunctionsMetaplectic.Construction.dot (-x) y)
      simp only [FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
      exact mul_comm _ _
  change (∫ x, @inner ℂ ℂ _
    (VectorFourier.fourierIntegral (FourierTools.Construction.circleCharacter ψ hu) μ (dotProductBilin k k) f.val x)
    (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x) ∂μ) =
      ∫ x, @inner ℂ ℂ _ (f.val x)
        (VectorFourier.fourierIntegral (FourierTools.Construction.circleCharacter ψ hu) μ
          (-(dotProductBilin k k).flip) (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x) ∂μ at h
  rw [← FourierTools.Construction.fourierIntegral_eq_vectorFourier ψ hu] at h
  simp_rw [hneg] at h
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using h

theorem testFourier_unitary (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.l2Energy k n (testFourier ψ hu hc μ hStable hInv f) = FunctionsMetaplectic.Construction.l2Energy k n f := by
  let ν : Measure (FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
  have hν := Measure.isAddLeftInvariant_eq_smul ν μ
  change (∫ x, ‖(testFourier ψ hu hc μ hStable hInv f).val x‖ ^ 2 ∂ν) =
    ∫ x, ‖f.val x‖ ^ 2 ∂ν
  rw [hν, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  congr 1
  exact fourierIntegral_norm_sq ψ hu hc μ hStable hInv f

omit [LocallyCompactSpace k] in
theorem testFourier_intertwines [CharZero k]
    (v : FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      FunctionsMetaplectic.Construction.heisenbergGraph ψ (FunctionsMetaplectic.Construction.symplecticAction (Generators.Construction.weylSymplectic k n) v)
        (testFourier ψ hu hc μ hStable hInv f) (testFourier ψ hu hc μ hStable hInv h) := by
  unfold FunctionsMetaplectic.Construction.heisenbergGraph
  rw [testFourier_apply, testFourier_apply]
  constructor
  · intro hh
    rw [hh, fourierIntegral_heisenberg]
  · intro hh
    have h2 := congrArg (FunctionsMetaplectic.Construction.fourierIntegral ψ μ) hh
    rw [fourierIntegral_heisenberg] at h2
    funext x
    have hx := congrFun h2 (-x)
    rw [hInv h, neg_neg] at hx
    have he := funext (hInv f)
    rw [he, heisenbergFunction_weyl_twice_reflect] at hx
    exact hx

/-- The raw Fourier operator in the independently defined oscillator
extension. Only stability and inversion remain as analytic inputs. -/
def fourierOscillator [CharZero k] : FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  ⟨(Generators.Construction.weylSymplectic k n, testFourier ψ hu hc μ hStable hInv),
    ⟨testFourier_unitary ψ hu hc μ hStable hInv,
      testFourier_intertwines ψ hu hc μ hStable hInv⟩⟩

theorem fourierOscillator_apply [CharZero k] (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    ((fourierOscillator ψ hu hc μ hStable hInv).val.2 f).val x =
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x := rfl

end

end OAI.RepresentationTheory.Weil.Local.FourierEquivalence.Construction
