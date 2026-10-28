import OAI.RepresentationTheory.Weil.Local.GeneralSchur
import OAI.RepresentationTheory.Weil.Local.BareGeneration

/-! # Complex Bare Kernel -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexBareKernel.Construction

noncomputable section

section

/-! A conjugate-linear symmetry of the complex quadratic and Fourier operators. -/

open _root_.MeasureTheory
open scoped ComplexConjugate NNReal

theorem complex_bruhat_conjugate_mem {n : ℕ} (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    (fun x => conj (f.val x)) ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := by
  obtain ⟨φ, hφ⟩ := ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mp f.property
  refine ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mpr ⟨φ.postcompCLM Complex.conjCLE.toContinuousLinearMap, ?_⟩
  rw [hφ]
  rfl

def complexRealStructure {n : ℕ} (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n :=
  ⟨fun x => conj (f.val (Complex.I • x)),
    complex_bruhat_conjugate_mem (FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv
      (CharacterScaling.Construction.scalarPositionEquiv n Complex.I Complex.I_ne_zero).toContinuousAddEquiv f)⟩

theorem complexRealStructure_smul {n : ℕ} (c : ℂ) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    complexRealStructure (c • f) = conj c • complexRealStructure f := by
  apply Subtype.ext
  funext x
  exact map_mul (starRingEnd ℂ) c (f.val (Complex.I • x))

theorem complexRealStructure_neg {n : ℕ} (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    complexRealStructure (-f) = -complexRealStructure f := by
  apply Subtype.ext
  funext x
  exact map_neg (starRingEnd ℂ) (f.val (Complex.I • x))

theorem complexRealStructure_quadratic {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z)) (hu : ∀ z, ‖ψ z‖ = 1)
    (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    (ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu B).val.val.2 (complexRealStructure f) =
      complexRealStructure ((ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu B).val.val.2 f) := by
  apply Subtype.ext
  funext x
  change ψ (FunctionsMetaplectic.Construction.quadratic B.val x) * conj (f.val (Complex.I • x)) =
    conj (ψ (FunctionsMetaplectic.Construction.quadratic B.val (Complex.I • x)) * f.val (Complex.I • x))
  rw [QuadraticIntertwiner.Construction.quadratic_smul_vector, Complex.I_sq, neg_one_mul, GaussianNonarchimedean.Construction.unitary_character_neg ψ hu, map_mul,
    starRingEnd_self_apply]

theorem haarModulus_complex_I : DeterminantMeasure.Construction.haarModulus ℂ Complex.I = 1 := by
  apply (pow_eq_one_iff_of_nonneg (show 0 ≤ DeterminantMeasure.Construction.haarModulus ℂ Complex.I from zero_le)
    (by decide : (4 : ℕ) ≠ 0)).mp
  rw [← map_pow]
  norm_num

theorem dot_complex_I {n : ℕ} (x y : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.dot (Complex.I • x) (Complex.I • y) = -FunctionsMetaplectic.Construction.dot x y := by
  simp only [FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = Complex.I ^ 2 * (x i * y i) := by ring
    _ = _ := by rw [Complex.I_sq, neg_one_mul]

theorem fourier_complexRealStructure {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hu : ∀ z, ‖ψ z‖ = 1)
    (μ : Measure ℂ) [μ.IsAddHaarMeasure] (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (complexRealStructure f).val x =
      conj (FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f.val (Complex.I • x)) := by
  let g : FunctionsMetaplectic.Construction.Position ℂ n → ℂ := fun z => conj (f.val z) * ψ (FunctionsMetaplectic.Construction.dot (Complex.I • x) z)
  have h := CharacterScaling.Construction.integral_scalar_position n Complex.I Complex.I_ne_zero μ g
  rw [haarModulus_complex_I] at h
  simp only [NNReal.coe_one, one_pow, inv_one, one_smul] at h
  calc
    _ = ∫ y, g (Complex.I • y) ∂Measure.pi (fun _ : Fin n => μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change conj (f.val (Complex.I • y)) * ψ (-FunctionsMetaplectic.Construction.dot x y) =
          conj (f.val (Complex.I • y)) * ψ (FunctionsMetaplectic.Construction.dot (Complex.I • x) (Complex.I • y))
        rw [dot_complex_I]
    _ = ∫ y, g y ∂Measure.pi (fun _ : Fin n => μ) := h
    _ = _ := by
      rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_conj]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        change conj (f.val y) * ψ (FunctionsMetaplectic.Construction.dot (Complex.I • x) y) =
          conj (f.val y * ψ (-FunctionsMetaplectic.Construction.dot (Complex.I • x) y))
        rw [map_mul, GaussianNonarchimedean.Construction.unitary_character_neg ψ hu, starRingEnd_self_apply]

theorem complexRealStructure_fourier {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    (ComplexCover.Construction.complexRawFourierOscillator n ψ hc hu hn).val.2 (complexRealStructure f) =
      complexRealStructure ((ComplexCover.Construction.complexRawFourierOscillator n ψ hc hu hn).val.2 f) := by
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure := (ComplexCover.Construction.complex_analytic_normalization ψ hc hu hn n).2.1
  apply Subtype.ext
  funext x
  rw [ComplexCover.Construction.complexRawFourierOscillator_apply]
  change _ = conj (((ComplexCover.Construction.complexRawFourierOscillator n ψ hc hu hn).val.2 f).val (Complex.I • x))
  rw [ComplexCover.Construction.complexRawFourierOscillator_apply]
  exact fourier_complexRealStructure ψ hu (FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ) f x

end

/-! The intrinsic complex bare cover has only the two scalar signs in its kernel. -/

open scoped ComplexConjugate

def complexRealSubgroup (n : ℕ) (ψ : AddChar ℂ ℂ) : Subgroup (FunctionsMetaplectic.Construction.Oscillator ℂ n ψ) where
  carrier := {a | ∀ f, a.val.2 (complexRealStructure f) = complexRealStructure (a.val.2 f)}
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb f
    change a.val.2 (b.val.2 (complexRealStructure f)) = complexRealStructure (a.val.2 (b.val.2 f))
    rw [hb, ha]
  inv_mem' := by
    intro a ha f
    change a.val.2.symm (complexRealStructure f) = complexRealStructure (a.val.2.symm f)
    apply a.val.2.injective
    rw [LinearEquiv.apply_symm_apply, ha, LinearEquiv.apply_symm_apply]

theorem complexRealSubgroup_projection (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) :
    (complexRealSubgroup n ψ).map (OscillatorProjection.Construction.oscillatorProjection ℂ n ψ) = ⊤ := by
  let H := complexRealSubgroup n ψ
  let w := ComplexCover.Construction.complexRawFourierOscillator n ψ hc hu hn
  have hw : w ∈ H := complexRealStructure_fourier ψ hc hu hn
  have hwπ : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ w = Generators.Construction.weylSymplectic ℂ n := rfl
  have hU (B : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n) : (ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu B).val ∈ H :=
    complexRealStructure_quadratic ψ hc hu B
  apply GenerationSymplectic.Construction.subgroup_eq_top_of_symplectic_unipotents
  · intro B
    let u := ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu ⟨-B.val, B.property.neg⟩
    refine ⟨w⁻¹ * u.val * w, H.mul_mem (H.mul_mem (H.inv_mem hw) (hU _)) hw, ?_⟩
    rw [map_mul, map_mul, map_inv, hwπ]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℂ n B).symm
  · intro B
    exact ⟨(ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu B).val, hU B, rfl⟩

theorem complex_metaplectic_le_realSubgroup (n : ℕ)
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) :
    FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ ≤ complexRealSubgroup n ψ := by
  let H := complexRealSubgroup n ψ
  have hsurj := complexRealSubgroup_projection n ψ hc hu hn
  have hnd : ¬ DiscreteTopology ℂ := by
    intro h
    let : DiscreteTopology ℂ := h
    have : Subsingleton ℂ := subsingleton_of_preconnected_totallyDisconnected
    exact zero_ne_one (Subsingleton.elim (0 : ℂ) 1)
  have hder : commutator (FunctionsMetaplectic.Construction.Oscillator ℂ n ψ) ≤ H :=
    BareGeneration.Construction.commutator_le_of_central_kernel (OscillatorProjection.Construction.oscillatorProjection ℂ n ψ) H
      (fun x => by
        have h : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ x ∈ H.map (OscillatorProjection.Construction.oscillatorProjection ℂ n ψ) := by rw [hsurj]; trivial
        exact h)
      (fun z hz x => GeneralSchur.Construction.oscillator_kernel_central hnd ψ hc hu hn z hz x)
  change Subgroup.closure (commutatorSet (FunctionsMetaplectic.Construction.Oscillator ℂ n ψ) ∪ {FunctionsMetaplectic.Construction.oscillatorMinus ℂ n ψ}) ≤ H
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with hx | hx
  · apply hder
    rw [commutator_eq_closure]
    exact Subgroup.subset_closure hx
  · obtain rfl := Set.mem_singleton_iff.mp hx
    intro f
    exact (complexRealStructure_neg f).symm

theorem complex_metaplectic_kernel_sign {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1)
    (a : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ) (ha : FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ a = 1) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n, a.val.val.2 f = ε • f := by
  obtain ⟨z, hz, hscalar⟩ := OscillatorSchur.Construction.complex_oscillator_kernel_scalar ψ hc hu hn a.val ha
  have hcomm := complex_metaplectic_le_realSubgroup n ψ hc hu hn a.property
  by_cases he : ∃ f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n, f ≠ 0
  · obtain ⟨f, hf⟩ := he
    obtain ⟨y, hy⟩ : ∃ y, f.val y ≠ 0 := by
      by_contra! h
      exact hf (Subtype.ext (funext h))
    have hh := hcomm f
    rw [hscalar, hscalar, complexRealStructure_smul] at hh
    have hv := congrArg (fun g : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n => g.val ((-Complex.I) • y)) hh
    have hxy : Complex.I • ((-Complex.I) • y) = y := by
      rw [smul_smul]
      norm_num
    change z * conj (f.val (Complex.I • ((-Complex.I) • y))) =
      conj z * conj (f.val (Complex.I • ((-Complex.I) • y))) at hv
    rw [hxy] at hv
    have hreal : z = conj z := mul_right_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hy) hv
    refine ⟨z, ?_, hscalar⟩
    calc
      z ^ 2 = z * conj z := by rw [← hreal, pow_two]
      _ = 1 := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]; norm_num
  · refine ⟨1, one_pow 2, fun f => ?_⟩
    have hf : f = 0 := by by_contra h; exact he ⟨f, h⟩
    rw [hf, map_zero, smul_zero]

theorem complex_metaplectic_same_projection_sign {n : ℕ}
    (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1)
    (a b : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ)
    (hab : FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ a = FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ b) :
    ∃ ε : ℂ, ε ^ 2 = 1 ∧ ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n,
      FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ a f = ε • FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ b f := by
  have hker : FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
  obtain ⟨ε, hε, h⟩ := complex_metaplectic_kernel_sign ψ hc hu hn (a * b⁻¹) hker
  refine ⟨ε, hε, fun f => ?_⟩
  have hh := h (b.val.val.2 f)
  change a.val.val.2 (b.val.val.2.symm (b.val.val.2 f)) = ε • b.val.val.2 f at hh
  simpa only [LinearEquiv.symm_apply_apply] using! hh

end

end OAI.RepresentationTheory.Weil.Local.ComplexBareKernel.Construction
