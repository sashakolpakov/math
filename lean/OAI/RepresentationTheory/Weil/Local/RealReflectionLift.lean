import OAI.RepresentationTheory.Weil.Local.ReflectionAlgebra
import OAI.RepresentationTheory.Weil.Local.RealWeyl

/-! # Real Reflection Lift -/

namespace OAI.RepresentationTheory.Weil.Local.RealReflectionLift.Construction

noncomputable section

section

/-! The exact Fourier–quadratic relation for real diagonal reflections. -/

open _root_.MeasureTheory _root_.Matrix

theorem reflection_fourier_quadratic_shift
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (a : Fin n → k) (ha : ∀ i, a i ^ 2 = 1) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (diagonal a) (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f)) x =
      ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal a) x) * ∫ y,
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun z => f z * ψ (-FunctionsMetaplectic.Construction.dot (fun i => a i * x i) z)) y *
          ψ (FunctionsMetaplectic.Construction.quadratic (diagonal a) y) ∂μ := by
  rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_add_right_eq_self _ (fun i => a i * x i), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.quadraticOperator_apply, NormalizedFresnel.Construction.fourierIntegral_modulation]
    have hp : ψ (FunctionsMetaplectic.Construction.quadratic (diagonal a) (y + fun i => a i * x i)) *
        ψ (-FunctionsMetaplectic.Construction.dot x (y + fun i => a i * x i)) =
        ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal a) x) * ψ (FunctionsMetaplectic.Construction.quadratic (diagonal a) y) := by
      rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
      congr 1
      simpa only [sub_eq_add_neg, add_comm] using ReflectionAlgebra.Construction.diagonal_reflection_complete_square a ha x y
    calc
      _ = (ψ (FunctionsMetaplectic.Construction.quadratic (diagonal a) (y + fun i => a i * x i)) *
          ψ (-FunctionsMetaplectic.Construction.dot x (y + fun i => a i * x i))) * FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (y + fun i => a i * x i) := by ring
      _ = _ := by rw [hp]; ring

theorem real_reflection_fourier_quadratic_fourier {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ^ 2 = 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c))
      (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (diagonal a)
        (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val)) x =
      (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (diagonal a) x) *
        FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c))
          (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-diagonal a) f.val) (fun i => a i * x i) := by
  let : (FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter c)).IsAddHaarMeasure :=
    FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ (Gaussian.Construction.realCharacter c) (RealFourierLp.Construction.fourierHaarScaleSquared_real_pos c hc)
  let μ := FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n := ⟨fun z => f.val z * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot (fun i => a i * x i) z),
    RealWeyl.Construction.real_modulation_mem c f (fun i => a i * x i)⟩
  have hpair := RealDiagonalNormalization.Construction.real_reflection_fresnel_pairing c hc a ha g
  have hmod : (∫ y, g.val y * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (diagonal a) y) ∂μ) =
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) μ (FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-diagonal a) f.val)
        (fun i => a i * x i) := by
    unfold FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change (f.val y * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot (fun i => a i * x i) y)) *
        Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (diagonal a) y) =
        (Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (-diagonal a) y) * f.val y) *
          Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.dot (fun i => a i * x i) y)
      rw [FunctionsMetaplectic.Construction.quadratic_neg]
      ring
  rw [reflection_fourier_quadratic_shift (Gaussian.Construction.realCharacter c) μ a ha, hpair, hmod]
  ring

theorem real_reflection_fourier_quadratic_relation {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ^ 2 = 1) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    let L := (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (ReflectionAlgebra.Construction.diagonalReflection a ha)).val.2
    let T := L * RealFourierFamily.Construction.realNormalizedFourier n c hc
    let P := QuadraticIntertwiner.Construction.testQuadratic (Gaussian.Construction.realCharacter c) (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property) (diagonal a)
    T (P (T f)) = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) • P.symm (T (P.symm f)) := by
  let D := ReflectionAlgebra.Construction.diagonalReflection a ha
  let L := (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) D).val.2
  let F := RealFourierFamily.Construction.realNormalizedFourier n c hc
  let P := QuadraticIntertwiner.Construction.testQuadratic (Gaussian.Construction.realCharacter c) (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property) (diagonal a)
  have hLL (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : L (L g) = g := by
    have h := LinearOscillatorHom.Construction.linearOscillator_mul (Gaussian.Construction.realCharacter c) D D
    rw [ReflectionAlgebra.Construction.diagonalReflection_square, LinearOscillatorHom.Construction.linearOscillator_one] at h
    exact congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter c) => b.val.2 g) h.symm
  have hLP (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : L (P g) = P (L g) := by
    apply Subtype.ext
    funext x
    change ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (ReflectionAlgebra.Construction.diagonalReflection a ha)).val.2 (P g)).val x = _
    rw [ReflectionAlgebra.Construction.linearOscillator_diagonalReflection_apply]
    change Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (diagonal a) (fun i => a i * x i)) * g.val (fun i => a i * x i) =
      Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (diagonal a) x) * ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (ReflectionAlgebra.Construction.diagonalReflection a ha)).val.2 g).val x
    rw [ReflectionAlgebra.Construction.linearOscillator_diagonalReflection_apply, ReflectionAlgebra.Construction.diagonal_reflection_quadratic a ha]
  have hFL (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : F (L g) = L (F g) := by
    let μ := FunctionsMetaplectic.Construction.selfDualMeasure ℝ (Gaussian.Construction.realCharacter c)
    let : μ.IsAddHaarMeasure := FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ (Gaussian.Construction.realCharacter c)
      (RealFourierLp.Construction.fourierHaarScaleSquared_real_pos c hc)
    have h := SymmetricSquareLift.Construction.fourierOscillator_linear_symmetric (Gaussian.Construction.realCharacter c) μ (RealFourierFamily.Construction.realFourierOscillatorFamily n c hc)
      rfl (RealFourierFamily.Construction.realNormalizedFourier_apply c hc) D (isSymm_diagonal a)
    rw [ReflectionAlgebra.Construction.diagonalReflection_inv] at h
    exact congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter c) => b.val.2 g) h
  change L (F (P (L (F f)))) = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) • P.symm (L (F (P.symm f)))
  rw [← hLP, hFL, hLL]
  have hF (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (F g).val =
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) g.val :=
    funext (RealFourierFamily.Construction.realNormalizedFourier_apply c hc g)
  have hP (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (P g).val = FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (diagonal a) g.val := rfl
  have hN (g : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : (P.symm g).val = FunctionsMetaplectic.Construction.quadraticOperator (Gaussian.Construction.realCharacter c) (-diagonal a) g.val := rfl
  apply Subtype.ext
  change (F (P (F f))).val = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) • (P.symm (L (F (P.symm f)))).val
  rw [hF, hP, hF, hN]
  funext x
  change _ = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) *
    (Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (-diagonal a) x) *
      ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (ReflectionAlgebra.Construction.diagonalReflection a ha)).val.2 (F (P.symm f))).val x)
  rw [ReflectionAlgebra.Construction.linearOscillator_diagonalReflection_apply, hF, hN, FunctionsMetaplectic.Construction.quadratic_neg, ← mul_assoc]
  exact real_reflection_fourier_quadratic_fourier c hc a ha f x

end

/-! Actual bare lifts of real diagonal reflections, with their Gaussian coefficients. -/

open _root_.Matrix

theorem exists_real_reflection_weyl_metaplectic {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ^ 2 = 1) :
    ∃ v : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c),
      FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c) v = Generators.Construction.leviSymplectic (ReflectionAlgebra.Construction.diagonalReflection a ha) * Generators.Construction.weylSymplectic ℝ n ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
        FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) v f =
          (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i))⁻¹ •
            (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (ReflectionAlgebra.Construction.diagonalReflection a ha)).val.2 (RealFourierFamily.Construction.realNormalizedFourier n c hc f) := by
  let D := ReflectionAlgebra.Construction.diagonalReflection a ha
  let l := LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) D
  let w := RealFourierFamily.Construction.realFourierOscillatorFamily n c hc
  let t := l * w
  let B : FunctionsMetaplectic.Construction.SymmetricMatrix ℝ n := ⟨diagonal a, isSymm_diagonal a⟩
  let u := QuadraticIntertwiner.Construction.realQuadraticMetaplectic c ⟨-B.val, B.property.neg⟩
  have hconj : t⁻¹ * u.val * t ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c) := by
    have h := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).Normal).conj_mem u.val u.property t⁻¹
    simpa only [inv_inv] using h
  let v : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c) := ⟨u.val * (t⁻¹ * u.val * t) * u.val,
    (FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).mul_mem
      ((FunctionsMetaplectic.Construction.metaplecticSubgroup ℝ n (Gaussian.Construction.realCharacter c)).mul_mem u.property hconj) u.property⟩
  have huProj : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) u.val = Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ := rfl
  have hlProj : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) l = Generators.Construction.leviSymplectic D := rfl
  have hwProj : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) w = Generators.Construction.weylSymplectic ℝ n := rfl
  have hcomm : Commute (Generators.Construction.leviSymplectic D) (Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩) := by
    change Generators.Construction.leviSymplectic D * Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ =
      Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ * Generators.Construction.leviSymplectic D
    apply Subtype.ext
    have hlev : (Generators.Construction.leviSymplectic D).val = fromBlocks (diagonal a) 0 0 (diagonal a) := by
      rw [Generators.Construction.leviSymplectic_matrix, ReflectionAlgebra.Construction.diagonalReflection_inv]
      simp [D, ReflectionAlgebra.Construction.diagonalReflection]
    change (Generators.Construction.leviSymplectic D).val * fromBlocks 1 0 (-diagonal a) 1 =
      fromBlocks 1 0 (-diagonal a) 1 * (Generators.Construction.leviSymplectic D).val
    rw [hlev]
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add, mul_neg, neg_mul, neg_zero]
  have hcancel : (Generators.Construction.leviSymplectic D)⁻¹ * Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ * Generators.Construction.leviSymplectic D =
      Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ := by
    rw [hcomm.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]
  have hupper : OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) (t⁻¹ * u.val * t) = GenerationSymplectic.Construction.upperSymplectic B := by
    calc
      _ = (Generators.Construction.weylSymplectic ℝ n)⁻¹ *
          ((Generators.Construction.leviSymplectic D)⁻¹ * Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ * Generators.Construction.leviSymplectic D) *
          Generators.Construction.weylSymplectic ℝ n := by
        simp only [t, map_mul, map_inv, hlProj, hwProj, huProj, _root_.mul_inv_rev]
        group
      _ = _ := by rw [hcancel]; exact (OscillatorProjection.Construction.upper_quadratic_conjugation ℝ n B).symm
  refine ⟨v, ?_, ?_⟩
  · change OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c) (u.val * (t⁻¹ * u.val * t) * u.val) = _
    rw [map_mul, map_mul, huProj, hupper]
    exact ReflectionAlgebra.Construction.reflection_weyl_factorization a ha
  · let P := QuadraticIntertwiner.Construction.testQuadratic (Gaussian.Construction.realCharacter c) (fun B f => RealTestSpace.Construction.quadraticOperator_real_mem c B f.property) (diagonal a)
    have hN : u.val.val.2 = P.symm := by apply LinearEquiv.ext; intro f; rfl
    have hΓ : (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      have hai : a i ≠ 0 := by
        intro h
        have hh := ha i
        rw [h, zero_pow (by decide)] at hh
        exact zero_ne_one hh
      intro h
      have hh := Gaussian.Construction.gaussianIndex_real_norm c (a i) hc hai
      rw [h, norm_zero] at hh
      exact zero_ne_one hh
    have hword := NormalizedFresnel.Construction.linearEquiv_weyl_word t.val.2 P (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) hΓ
      (real_reflection_fourier_quadratic_relation c hc a ha)
    intro f
    have hop : FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) v f =
        P.symm (t.val.2.symm (P.symm (t.val.2 (P.symm f)))) := by
      change ((u.val.val.2 * ((t.val.2)⁻¹ * u.val.val.2 * t.val.2)) * u.val.val.2) f = _
      rw [hN]
      rfl
    rw [hop, hword]
    rfl

theorem exists_real_diagonal_reflection_metaplectic {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ^ 2 = 1) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c),
      FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c) m = Generators.Construction.leviSymplectic (ReflectionAlgebra.Construction.diagonalReflection a ha) ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) m f).val x =
          ((∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n) *
            f.val (fun i => a i * x i) := by
  obtain ⟨v, hv, hvo⟩ := exists_real_reflection_weyl_metaplectic c hc a ha
  obtain ⟨w, hw, hwo⟩ := RealWeyl.Construction.exists_real_weyl_metaplectic_parameter n c hc
  let D := ReflectionAlgebra.Construction.diagonalReflection a ha
  let L := (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) D).val.2
  have hLL (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) : L (L f) = f := by
    have h := LinearOscillatorHom.Construction.linearOscillator_mul (Gaussian.Construction.realCharacter c) D D
    rw [ReflectionAlgebra.Construction.diagonalReflection_square, LinearOscillatorHom.Construction.linearOscillator_one] at h
    exact congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter c) => b.val.2 f) h.symm
  have hlevSq : Generators.Construction.leviSymplectic D * Generators.Construction.leviSymplectic D = 1 := by
    have h := LinearOscillatorHom.Construction.linearOscillator_mul (Gaussian.Construction.realCharacter c) D D
    rw [ReflectionAlgebra.Construction.diagonalReflection_square, LinearOscillatorHom.Construction.linearOscillator_one] at h
    exact congrArg (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c)) h.symm
  have hlevInv : (Generators.Construction.leviSymplectic D)⁻¹ = Generators.Construction.leviSymplectic D := inv_eq_of_mul_eq_one_right hlevSq
  refine ⟨w * v⁻¹, ?_, fun f x => ?_⟩
  · rw [map_mul, map_inv, hw, hv, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul, hlevInv]
  · let g := FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) v⁻¹ f
    have hvg : FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) v g = f := by
      change v.val.val.2 (v.val.val.2.symm f) = f
      exact LinearEquiv.apply_symm_apply _ _
    have he := congrArg L (hvo g)
    rw [hvg, map_smul, hLL] at he
    have hΓ : (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      have hai : a i ≠ 0 := by
        intro h
        have hh := ha i
        rw [h, zero_pow (by decide)] at hh
        exact zero_ne_one hh
      intro h
      have hh := Gaussian.Construction.gaussianIndex_real_norm c (a i) hc hai
      rw [h, norm_zero] at hh
      exact zero_ne_one hh
    have hF : RealFourierFamily.Construction.realNormalizedFourier n c hc g = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) • L f := by
      have h := congrArg (fun z : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n => (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) • z) he
      simpa only [smul_smul, mul_inv_cancel₀ hΓ, one_smul] using h.symm
    change (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) w g).val x = _
    rw [hwo, ← RealFourierFamily.Construction.realNormalizedFourier_apply c hc, hF]
    change (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n)⁻¹ *
      ((∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) *
        ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (ReflectionAlgebra.Construction.diagonalReflection a ha)).val.2 f).val x) = _
    rw [ReflectionAlgebra.Construction.linearOscillator_diagonalReflection_apply]
    ring

end

end OAI.RepresentationTheory.Weil.Local.RealReflectionLift.Construction
