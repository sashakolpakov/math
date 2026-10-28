import OAI.RepresentationTheory.Weil.AdelicSplitting.FourierTools
import OAI.RepresentationTheory.Weil.AdelicSplitting.NonarchimedeanIntertwiner

/-! # Fourier Intertwiner -/

namespace OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner.LocalAnalysis

noncomputable section

/-! Fourier covariance and construction of the raw Fourier oscillator from inversion. -/

open _root_.MeasureTheory
open scoped BigOperators

theorem positionPart_weyl {k : Type} [Field k] {n : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n) :
    NonarchimedeanIntertwiner.LocalAnalysis.positionPart (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k n) v) = NonarchimedeanIntertwiner.LocalAnalysis.momentumPart v := by
  funext i
  simp [NonarchimedeanIntertwiner.LocalAnalysis.positionPart, NonarchimedeanIntertwiner.LocalAnalysis.momentumPart, Local.FunctionsMetaplectic.Construction.symplecticAction, Local.Generators.Construction.weylSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem momentumPart_weyl {k : Type} [Field k] {n : ℕ} (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n) :
    NonarchimedeanIntertwiner.LocalAnalysis.momentumPart (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k n) v) = -NonarchimedeanIntertwiner.LocalAnalysis.positionPart v := by
  funext i
  simp [NonarchimedeanIntertwiner.LocalAnalysis.positionPart, NonarchimedeanIntertwiner.LocalAnalysis.momentumPart, Local.FunctionsMetaplectic.Construction.symplecticAction, Local.Generators.Construction.weylSymplectic_matrix,
    Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem fourierIntegral_heisenberg
    {k : Type} [NormedField k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) :
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f) =
      Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k n) v)
        (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f) := by
  funext x
  rw [NonarchimedeanIntertwiner.LocalAnalysis.heisenbergFunction_eq_dot, positionPart_weyl, momentumPart_weyl]
  unfold Local.FunctionsMetaplectic.Construction.fourierIntegral
  rw [← integral_add_right_eq_self
    (fun y => Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f y * ψ (-Local.FunctionsMetaplectic.Construction.dot x y)) (NonarchimedeanIntertwiner.LocalAnalysis.positionPart v)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [NonarchimedeanIntertwiner.LocalAnalysis.heisenbergFunction_eq_dot, add_sub_cancel_right]
    have hphase :
        Local.FunctionsMetaplectic.Construction.dot (NonarchimedeanIntertwiner.LocalAnalysis.momentumPart v) (y + NonarchimedeanIntertwiner.LocalAnalysis.positionPart v - (2 : k)⁻¹ • NonarchimedeanIntertwiner.LocalAnalysis.positionPart v) -
          Local.FunctionsMetaplectic.Construction.dot x (y + NonarchimedeanIntertwiner.LocalAnalysis.positionPart v) =
        Local.FunctionsMetaplectic.Construction.dot (-NonarchimedeanIntertwiner.LocalAnalysis.positionPart v) (x - (2 : k)⁻¹ • NonarchimedeanIntertwiner.LocalAnalysis.momentumPart v) -
          Local.FunctionsMetaplectic.Construction.dot (x - NonarchimedeanIntertwiner.LocalAnalysis.momentumPart v) y := by
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    calc
      _ = ψ (Local.FunctionsMetaplectic.Construction.dot (NonarchimedeanIntertwiner.LocalAnalysis.momentumPart v)
          (y + NonarchimedeanIntertwiner.LocalAnalysis.positionPart v - (2 : k)⁻¹ • NonarchimedeanIntertwiner.LocalAnalysis.positionPart v) - Local.FunctionsMetaplectic.Construction.dot x (y + NonarchimedeanIntertwiner.LocalAnalysis.positionPart v)) * f y := by
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring
      _ = _ := by
        rw [hphase]
        simp only [sub_eq_add_neg, ψ.map_add_eq_mul]
        ring

theorem heisenbergFunction_weyl_twice_reflect
    {k : Type} [Field k] {n : ℕ} (ψ : AddChar k ℂ)
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f : Local.FunctionsMetaplectic.Construction.Position k n → ℂ) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ
      (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k n) (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k n) v))
      (fun y => f (-y)) (-x) = Local.FunctionsMetaplectic.Construction.heisenbergFunction ψ v f x := by
  rw [NonarchimedeanIntertwiner.LocalAnalysis.heisenbergFunction_eq_dot, NonarchimedeanIntertwiner.LocalAnalysis.heisenbergFunction_eq_dot,
    positionPart_weyl, momentumPart_weyl, positionPart_weyl, momentumPart_weyl]
  congr 2
  · simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · funext i
    simp [sub_eq_add_neg, add_comm]

variable {k : Type} [NormedField k] [LocallyCompactSpace k]
  [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (ψ : AddChar k ℂ) (hu : ∀ t, ‖ψ t‖ = 1) (hc : Continuous ψ)
  (μ : Measure (Local.FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
  (hStable : ∀ f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n, Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val ∈ Local.FunctionsMetaplectic.Construction.schwartzBruhat k n)
  (hInv : ∀ (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) x,
    Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = f.val (-x))

def testFourierLinear : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n →ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k n :=
  (FourierTools.LocalAnalysis.schwartzBruhat_fourierLinearMap n ψ hu hc μ).codRestrict _ hStable

include hInv

omit [LocallyCompactSpace k] in
theorem testFourierLinear_square (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    (testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable f)).val x =
      f.val (-x) := hInv f x

omit [LocallyCompactSpace k] in
theorem testFourierLinear_fourth (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable
      (testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable f))) = f := by
  apply Subtype.ext
  funext x
  rw [testFourierLinear_square ψ hu hc μ hStable hInv,
    testFourierLinear_square ψ hu hc μ hStable hInv, neg_neg]

def testFourier : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n ≃ₗ[ℂ] Local.FunctionsMetaplectic.Construction.schwartzBruhat k n where
  toLinearMap := testFourierLinear ψ hu hc μ hStable
  invFun f := testFourierLinear ψ hu hc μ hStable
    (testFourierLinear ψ hu hc μ hStable (testFourierLinear ψ hu hc μ hStable f))
  left_inv := testFourierLinear_fourth ψ hu hc μ hStable hInv
  right_inv := testFourierLinear_fourth ψ hu hc μ hStable hInv

omit [LocallyCompactSpace k] in
theorem testFourier_apply (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (testFourier ψ hu hc μ hStable hInv f).val = Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val := rfl

include hu hc hStable in
theorem fourierIntegral_norm_sq (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, ‖Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x‖ ^ 2 ∂μ) = ∫ x, ‖f.val x‖ ^ 2 ∂μ := by
  have hf := TestSpace.LocalAnalysis.schwartzBruhat_integrable μ f
  have hg := TestSpace.LocalAnalysis.schwartzBruhat_integrable μ (testFourierLinear ψ hu hc μ hStable f)
  have h := VectorFourier.integral_sesq_fourierIntegral_eq_neg_flip
    (innerSL ℂ) (L := dotProductBilin k k)
    (FourierTools.LocalAnalysis.circleCharacter_continuous ψ hu hc) (FourierTools.LocalAnalysis.dotProductBilin_continuous n) hf hg
  have hneg (x : Local.FunctionsMetaplectic.Construction.Position k n) :
      VectorFourier.fourierIntegral (FourierTools.LocalAnalysis.circleCharacter ψ hu) μ
        (-(dotProductBilin k k).flip) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x = f.val x := by
    have hi := hInv f (-x)
    rw [neg_neg] at hi
    rw [← hi]
    unfold VectorFourier.fourierIntegral Local.FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [LinearMap.neg_apply, LinearMap.flip_apply,
        Circle.smul_def, smul_eq_mul]
      change ψ (- -Local.FunctionsMetaplectic.Construction.dot x y) * _ = _ * ψ (-Local.FunctionsMetaplectic.Construction.dot (-x) y)
      simp only [Local.FunctionsMetaplectic.Construction.dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, neg_neg]
      exact mul_comm _ _
  change (∫ x, @inner ℂ ℂ _
    (VectorFourier.fourierIntegral (FourierTools.LocalAnalysis.circleCharacter ψ hu) μ (dotProductBilin k k) f.val x)
    (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x) ∂μ) =
      ∫ x, @inner ℂ ℂ _ (f.val x)
        (VectorFourier.fourierIntegral (FourierTools.LocalAnalysis.circleCharacter ψ hu) μ
          (-(dotProductBilin k k).flip) (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val) x) ∂μ at h
  rw [← FourierTools.LocalAnalysis.fourierIntegral_eq_vectorFourier ψ hu] at h
  simp_rw [hneg] at h
  apply Complex.ofRealLI.injective
  simpa [← LinearIsometry.integral_comp_comm, inner_self_eq_norm_sq_to_K] using h

theorem testFourier_unitary (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Local.FunctionsMetaplectic.Construction.l2Energy k n (testFourier ψ hu hc μ hStable hInv f) = Local.FunctionsMetaplectic.Construction.l2Energy k n f := by
  let ν : Measure (Local.FunctionsMetaplectic.Construction.Position k n) := Measure.pi (fun _ : Fin n => (Measure.addHaar : Measure k))
  have hν := Measure.isAddLeftInvariant_eq_smul ν μ
  change (∫ x, ‖(testFourier ψ hu hc μ hStable hInv f).val x‖ ^ 2 ∂ν) =
    ∫ x, ‖f.val x‖ ^ 2 ∂ν
  rw [hν, integral_smul_nnreal_measure, integral_smul_nnreal_measure]
  congr 1
  exact fourierIntegral_norm_sq ψ hu hc μ hStable hInv f

omit [LocallyCompactSpace k] in
theorem testFourier_intertwines [CharZero k]
    (v : Local.FunctionsMetaplectic.Construction.PhaseSpace k n) (f h : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ v f h ↔
      Local.FunctionsMetaplectic.Construction.heisenbergGraph ψ (Local.FunctionsMetaplectic.Construction.symplecticAction (Local.Generators.Construction.weylSymplectic k n) v)
        (testFourier ψ hu hc μ hStable hInv f) (testFourier ψ hu hc μ hStable hInv h) := by
  unfold Local.FunctionsMetaplectic.Construction.heisenbergGraph
  rw [testFourier_apply, testFourier_apply]
  constructor
  · intro hh
    rw [hh, fourierIntegral_heisenberg]
  · intro hh
    have h2 := congrArg (Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ) hh
    rw [fourierIntegral_heisenberg] at h2
    funext x
    have hx := congrFun h2 (-x)
    rw [hInv h, neg_neg] at hx
    have he := funext (hInv f)
    rw [he, heisenbergFunction_weyl_twice_reflect] at hx
    exact hx

/-- The raw Fourier operator in the independently defined oscillator
extension. Only stability and inversion remain as analytic inputs. -/
def fourierOscillator [CharZero k] : Local.FunctionsMetaplectic.Construction.Oscillator k n ψ :=
  ⟨(Local.Generators.Construction.weylSymplectic k n, testFourier ψ hu hc μ hStable hInv),
    ⟨testFourier_unitary ψ hu hc μ hStable hInv,
      testFourier_intertwines ψ hu hc μ hStable hInv⟩⟩

theorem fourierOscillator_apply [CharZero k] (f : Local.FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : Local.FunctionsMetaplectic.Construction.Position k n) :
    ((fourierOscillator ψ hu hc μ hStable hInv).val.2 f).val x =
      Local.FunctionsMetaplectic.Construction.fourierIntegral ψ μ f.val x := rfl

end

end OAI.RepresentationTheory.Weil.AdelicSplitting.FourierIntertwiner.LocalAnalysis
