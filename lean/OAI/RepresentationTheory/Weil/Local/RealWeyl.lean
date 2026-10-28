import OAI.RepresentationTheory.Weil.Local.RealFresnelNormalization
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # Real Weyl -/

namespace OAI.RepresentationTheory.Weil.Local.RealWeyl.Construction

noncomputable section

/-! The exact Gaussian-normalized real Weyl generator lies in the intrinsic bare cover. -/

open _root_.MeasureTheory

theorem real_modulation_mem {n : ℕ} (c : ℝ) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (fun z => f.val z * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot x z)) ∈ FunctionsMetaplectic.Construction.schwartzBruhat ℝ n := by
  obtain ⟨φ, hφ⟩ := RealTestSpace.Construction.schwartzBruhat_real_iff.mp f.property
  have hp : Function.HasTemperateGrowth (fun z : FunctionsMetaplectic.Construction.Position ℝ n => -FunctionsMetaplectic.Construction.dot x z) := by
    exact (Function.HasTemperateGrowth.sum (fun i _ =>
      (Function.HasTemperateGrowth.const (x i)).mul
        (ContinuousLinearMap.proj i : FunctionsMetaplectic.Construction.Position ℝ n →L[ℝ] ℝ).hasTemperateGrowth)).neg
  refine RealTestSpace.Construction.schwartzBruhat_real_iff.mpr ⟨SchwartzMap.smulLeftCLM ℂ
    (fun z => Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot x z)) φ, ?_⟩
  funext z
  change f.val z * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot x z) =
    (SchwartzMap.smulLeftCLM ℂ (Gaussian.Construction.realCharacter c ∘ fun z => -FunctionsMetaplectic.Construction.dot x z) φ) z
  rw [SchwartzMap.smulLeftCLM_apply_apply ((RealTestSpace.Construction.realCharacter_temperate c).comp hp)]
  rw [← congrFun hφ z]
  exact mul_comm _ _

theorem real_fourier_quadratic_fourier {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c))
      (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) 1
        (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val)) x =
      FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) *
        FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c))
          (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-1) f.val) x := by
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter c)).IsAddHaarMeasure :=
    FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ (Gaussian.Construction.realCharacter c)
      (RealFourierLp.Construction.fourierHaarScaleSquared_real_pos c hc)
  let μ := FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n := ⟨fun z => f.val z * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot x z), real_modulation_mem c f x⟩
  have hpair := RealFresnelNormalization.Construction.real_fresnel_pairing c hc g
  calc
    _ = Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) * ∫ y,
        FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) μ g.val y * Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ :=
      NormalizedFresnel.Construction.fourier_quadratic_shift (Gaussian.Construction.realCharacter c) μ f.val x
    _ = Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n *
        ∫ y, g.val y * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 y) ∂μ) :=
      congrArg (fun z : ℂ => Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) * z) hpair
    _ = Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n *
        FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) μ (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-1) f.val) x) :=
      congrArg (fun z : ℂ => Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic 1 x) * (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n * z))
        (NormalizedFresnel.Construction.modulated_quadratic_integral (Gaussian.Construction.realCharacter c) μ f.val x)
    _ = _ := by ring

theorem real_fourier_quadratic_relation {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (T : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n ≃ₗ[ℂ] FunctionsMetaplectic.Construction.schwartzBruhat ℝ n)
    (hT : ∀ f x, (T f).val x = FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val x)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    let P := QuadraticIntertwiner.Construction.testQuadratic (Gaussian.Construction.realCharacter c) (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property) 1
    T (P (T f)) = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n • P.symm (T (P.symm f)) := by
  let P := QuadraticIntertwiner.Construction.testQuadratic (Gaussian.Construction.realCharacter c) (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property)
    (1 : Matrix (Fin n) (Fin n) ℝ)
  have hTf (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (T f).val =
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val := funext (hT f)
  have hP (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (P f).val = FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) 1 f.val := rfl
  have hN (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (P.symm f).val = FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-1) f.val := rfl
  change T (P (T f)) = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n • P.symm (T (P.symm f))
  apply Subtype.ext
  change (T (P (T f))).val = (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n) • (P.symm (T (P.symm f))).val
  rw [hTf, hP, hTf, hN, hTf, hN]
  funext x
  change _ = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n *
    (Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (-1) x) * FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c)
      (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-1) f.val) x)
  rw [FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc]
  exact real_fourier_quadratic_fourier c hc f x

theorem exists_real_weyl_metaplectic_parameter (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    ∃ w : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c),
      FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c) w = Generators.Construction.weylSymplectic ℝ n ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) w f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n)⁻¹ *
            FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val x := by
  let w := RealFourierFamily.Construction.realFourierOscillatorFamily n c hc
  let u := QuadraticIntertwiner.Construction.realQuadraticMetaplectic c (⟨-1, Matrix.isSymm_one.neg⟩ : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n)
  have hconj : w⁻¹ * u.val * w ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c) := by
    have h := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).Normal).conj_mem u.val u.property w⁻¹
    simpa only [inv_inv] using h
  let v : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c) := ⟨u.val * (w⁻¹ * u.val * w) * u.val,
    (FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).mul_mem
      ((FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).mul_mem u.property hconj) u.property⟩
  have hw : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) w = Generators.Construction.weylSymplectic ℝ n := rfl
  have huProj : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) u.val =
      Generators.Construction.quadraticSymplectic ⟨-1, Matrix.isSymm_one.neg⟩ := rfl
  have hupper : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) (w⁻¹ * u.val * w) =
      GenerationSymplectic.Construction.upperSymplectic ⟨1, Matrix.isSymm_one⟩ := by
    rw [map_mul, map_mul, map_inv, hw, huProj]
    exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℝ n ⟨1, Matrix.isSymm_one⟩).symm
  refine ⟨v, ?_, ?_⟩
  · change OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) (u.val * (w⁻¹ * u.val * w) * u.val) = _
    rw [map_mul, map_mul, huProj, hupper]
    exact NormalizedFresnel.Construction.weyl_lower_unipotent_factorization n
  · let P := QuadraticIntertwiner.Construction.testQuadratic (Gaussian.Construction.realCharacter c) (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property)
      (1 : Matrix (Fin n) (Fin n) ℝ)
    have hN : u.val.val.2 = P.symm := by apply LinearEquiv.ext; intro f; rfl
    have hγ : FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n ≠ 0 := pow_ne_zero _ (by
      intro hz
      have h := Gaussian.Construction.gaussianIndex_real_norm c 1 hc one_ne_zero
      rw [hz, norm_zero] at h
      exact zero_ne_one h)
    have hrel := real_fourier_quadratic_relation c hc w.val.2 (RealFourierFamily.Construction.realNormalizedFourier_apply c hc)
    have hword := NormalizedFresnel.Construction.linearEquiv_weyl_word w.val.2 P (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n) hγ hrel
    intro f x
    have hop : FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) v f =
        P.symm (w.val.2.symm (P.symm (w.val.2 (P.symm f)))) := by
      change ((u.val.val.2 * ((w.val.2)⁻¹ * u.val.val.2 * w.val.2)) * u.val.val.2) f = _
      rw [hN]
      rfl
    rw [hop, hword]
    change (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n)⁻¹ * (w.val.2 f).val x = _
    exact congrArg (fun z : ℂ => (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n)⁻¹ * z)
      (RealFourierFamily.Construction.realNormalizedFourier_apply c hc f x)

theorem exists_real_weyl_metaplectic (n : ℕ)
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) :
    ∃ w : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ, FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ w = Generators.Construction.weylSymplectic ℝ n ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ w f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ 1 ^ n)⁻¹ * FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) f.val x := by
  obtain ⟨c, hc', rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hn
  exact exists_real_weyl_metaplectic_parameter n c hc'

end

end OAI.RepresentationTheory.Weil.Local.RealWeyl.Construction
