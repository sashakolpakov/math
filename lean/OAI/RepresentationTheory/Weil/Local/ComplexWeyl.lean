import OAI.RepresentationTheory.Weil.Local.ComplexFresnelNormalization
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # Complex Weyl -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexWeyl.Construction

noncomputable section

/-! The exact Gaussian-normalized complex Weyl generator lies in the intrinsic bare cover. -/

open _root_.MeasureTheory

theorem complex_modulation_mem {n : ℕ} (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    (fun z => f.val z * ψ (-FunctionsMetaplectic.Construction.dot x z)) ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := by
  obtain ⟨φ, hφ⟩ := ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mp f.property
  have hp : Function.HasTemperateGrowth (fun z : FunctionsMetaplectic.Construction.Position ℂ n => -FunctionsMetaplectic.Construction.dot x z) := by
    exact (Function.HasTemperateGrowth.sum (fun i _ =>
      (Function.HasTemperateGrowth.const (x i)).mul
        (ContinuousLinearMap.proj i : FunctionsMetaplectic.Construction.Position ℂ n →L[ℝ] ℂ).hasTemperateGrowth)).neg
  refine ArchimedeanTestSpace.Construction.schwartzBruhat_archimedean_iff.mpr ⟨SchwartzMap.smulLeftCLM ℂ
    (fun z => ψ (-FunctionsMetaplectic.Construction.dot x z)) φ, ?_⟩
  funext z
  change f.val z * ψ (-FunctionsMetaplectic.Construction.dot x z) =
    (SchwartzMap.smulLeftCLM ℂ (ψ ∘ fun z => -FunctionsMetaplectic.Construction.dot x z) φ) z
  rw [SchwartzMap.smulLeftCLM_apply_apply ((ArchimedeanTestSpace.Construction.continuous_unitary_complex_character_temperate ψ hc hu).comp hp)]
  rw [← congrFun hφ z]
  exact mul_comm _ _

theorem complex_fourier_quadratic_fourier {n : ℕ} (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)
      (FunctionsMetaplectic.Construction.quadraticOperator ψ 1
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val)) x =
      FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n * ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ)
          (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x := by
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ).IsAddHaarMeasure :=
    (ComplexCover.Construction.complex_analytic_normalization ψ hc hu hn n).2.1
  let μ := FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let g : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n := ⟨fun z => f.val z * ψ (-FunctionsMetaplectic.Construction.dot x z), complex_modulation_mem ψ hc hu f x⟩
  have hpair := ComplexFresnelNormalization.Construction.complex_fresnel_pairing ψ hc hu hn g
  calc
    _ = ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * ∫ y,
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ g.val y * ψ (FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ :=
      NormalizedFresnel.Construction.fourier_quadratic_shift ψ μ f.val x
    _ = ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n *
        ∫ y, g.val y * ψ (-FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ) :=
      congrArg (fun z : ℂ => ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * z) hpair
    _ = ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n *
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x) :=
      congrArg (fun z : ℂ => ψ (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n * z))
        (NormalizedFresnel.Construction.modulated_quadratic_integral ψ μ f.val x)
    _ = _ := by ring

theorem complex_fourier_quadratic_relation {n : ℕ} (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1)
    (T : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat ℂ n)
    (hT : ∀ f x, (T f).val x = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val x)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) :
    let P := QuadraticIntertwiner.Construction.testQuadratic ψ (ArchimedeanTestSpace.Construction.quadratic_archimedean_mem ψ (ArchimedeanTestSpace.Construction.continuous_unitary_complex_character_temperate ψ hc hu)) 1
    T (P (T f)) = FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n • P.symm (T (P.symm f)) := by
  let P := QuadraticIntertwiner.Construction.testQuadratic ψ (ArchimedeanTestSpace.Construction.quadratic_archimedean_mem ψ (ArchimedeanTestSpace.Construction.continuous_unitary_complex_character_temperate ψ hc hu))
    (1 : Matrix (Fin n) (Fin n) ℂ)
  have hTf (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) : (T f).val =
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val := funext (hT f)
  have hP (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) : (P f).val = FunctionsMetaplectic.Construction.quadraticOperator ψ 1 f.val := rfl
  have hN (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) : (P.symm f).val = FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val := rfl
  change T (P (T f)) = FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n • P.symm (T (P.symm f))
  apply Subtype.ext
  change (T (P (T f))).val = (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n) • (P.symm (T (P.symm f))).val
  rw [hTf, hP, hTf, hN, hTf, hN]
  funext x
  change _ = FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n *
    (ψ (FunctionsMetaplectic.Construction.quadratic (-1) x) * FunctionsMetaplectic.Construction.fourierIntegral ψ
      (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) (FunctionsMetaplectic.Construction.quadraticOperator ψ (-1) f.val) x)
  rw [FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc]
  exact complex_fourier_quadratic_fourier ψ hc hu hn f x

theorem exists_complex_weyl_metaplectic (n : ℕ) (ψ : AddChar ℂ ℂ) (hc : Continuous (fun z => ψ z))
    (hu : ∀ z, ‖ψ z‖ = 1) (hn : ∃ z, ψ z ≠ 1) :
    ∃ w : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ,
      FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ w = Generators.Construction.weylSymplectic ℂ n ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ w f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n)⁻¹ *
            FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℂ n ψ) f.val x := by
  let w := ComplexCover.Construction.complexRawFourierOscillator n ψ hc hu hn
  let u := ArchimedeanTestSpace.Construction.complexQuadraticMetaplectic ψ hc hu (⟨-1, Matrix.isSymm_one.neg⟩ : FunctionsMetaplectic.Construction.SymmetricMatrix ℂ n)
  have hconj : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ := by
    have h := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ).Normal).conj_mem u.val u.property w⁻¹
    simpa only [inv_inv] using h
  let v : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ := ⟨u.val * (w⁻¹ * u.val * w) * u.val,
    (FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ).mul_mem
      ((FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ).mul_mem u.property hconj) u.property⟩
  have hw : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ w = Generators.Construction.weylSymplectic ℂ n := rfl
  have huProj : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ u.val =
      Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩ := rfl
  have hupper : OscillatorProjection.Construction.oscillatorProjection ℂ n ψ (w⁻¹ * u.val * w) =
      GenerationSymplectic.Construction.upperSymplectic ⟨1, Matrix.isSymm_one⟩ := by
    rw [map_mul, map_mul, map_inv, hw, huProj]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℂ n ⟨1, Matrix.isSymm_one⟩).symm
  refine ⟨v, ?_, ?_⟩
  · change OscillatorProjection.Construction.oscillatorProjection ℂ n ψ (u.val * (w⁻¹ * u.val * w) * u.val) = _
    rw [map_mul, map_mul, huProj, hupper]
    exact NormalizedFresnel.Construction.weyl_lower_unipotent_factorization n
  · let P := QuadraticIntertwiner.Construction.testQuadratic ψ (ArchimedeanTestSpace.Construction.quadratic_archimedean_mem ψ (ArchimedeanTestSpace.Construction.continuous_unitary_complex_character_temperate ψ hc hu))
      (1 : Matrix (Fin n) (Fin n) ℂ)
    have hN : u.val.val.2 = P.symm := by apply LinearEquiv.ext; intro f; rfl
    have hγ : FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n ≠ 0 := pow_ne_zero _ (by
      intro hz
      have h := FunctionsMetaplectic.Construction.gaussianIndex_norm ℂ ψ 1
        (ArchimedeanTestSpace.Construction.complex_gaussian_normalization ψ hc hu hn 1 one_ne_zero).2.1
      rw [hz, norm_zero] at h
      exact zero_ne_one h)
    have hrel := complex_fourier_quadratic_relation ψ hc hu hn w.val.2
      (ComplexCover.Construction.complexRawFourierOscillator_apply n ψ hc hu hn)
    have hword := NormalizedFresnel.Construction.linearEquiv_weyl_word w.val.2 P (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n) hγ hrel
    intro f x
    have hop : FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ v f =
        P.symm (w.val.2.symm (P.symm (w.val.2 (P.symm f)))) := by
      change ((u.val.val.2 * ((w.val.2)⁻¹ * u.val.val.2 * w.val.2)) * u.val.val.2) f = _
      rw [hN]
      rfl
    rw [hop, hword]
    change (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n)⁻¹ * (w.val.2 f).val x = _
    exact congrArg (fun z : ℂ => (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1 ^ n)⁻¹ * z)
      (ComplexCover.Construction.complexRawFourierOscillator_apply n ψ hc hu hn f x)

end

end OAI.RepresentationTheory.Weil.Local.ComplexWeyl.Construction
