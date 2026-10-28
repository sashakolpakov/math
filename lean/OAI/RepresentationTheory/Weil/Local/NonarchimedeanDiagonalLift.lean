import OAI.RepresentationTheory.Weil.Local.DiagonalAlgebra
import OAI.RepresentationTheory.Weil.Local.NormalizedFresnel

/-! # Nonarchimedean Diagonal Lift -/

namespace OAI.RepresentationTheory.Weil.Local.NonarchimedeanDiagonalLift.Construction

noncomputable section

section

/-! Fourier–quadratic composition for arbitrary nonarchimedean diagonal coefficients. -/

open _root_.Matrix _root_.MeasureTheory

theorem diagonal_fourier_quadratic_shift
    {k : Type} [NormedField k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
    [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure (FunctionsMetaplectic.Construction.Position k n)) [μ.IsAddHaarMeasure]
    (a : Fin n → kˣ) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (diagonal fun i => (a i).val) (FunctionsMetaplectic.Construction.fourierIntegral ψ μ f)) x =
      ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) * ∫ y,
        FunctionsMetaplectic.Construction.fourierIntegral ψ μ (fun z => f z * ψ (-FunctionsMetaplectic.Construction.dot (fun i => x i / (a i).val) z)) y *
          ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) y) ∂μ := by
  rw [FunctionsMetaplectic.Construction.fourierIntegral, ← integral_add_right_eq_self _ (fun i => x i / (a i).val), ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.quadraticOperator_apply, NormalizedFresnel.Construction.fourierIntegral_modulation]
    have hp : ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (y + fun i => x i / (a i).val)) *
        ψ (-FunctionsMetaplectic.Construction.dot x (y + fun i => x i / (a i).val)) =
        ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) *
          ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) y) := by
      rw [← ψ.map_add_eq_mul, ← ψ.map_add_eq_mul]
      congr 1
      simpa only [sub_eq_add_neg, add_comm] using DiagonalAlgebra.Construction.diagonal_complete_square a x y
    calc
      _ = (ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (y + fun i => x i / (a i).val)) *
          ψ (-FunctionsMetaplectic.Construction.dot x (y + fun i => x i / (a i).val))) *
            FunctionsMetaplectic.Construction.fourierIntegral ψ μ f (y + fun i => x i / (a i).val) := by ring
      _ = _ := by rw [hp]; ring

theorem nonarchimedean_diagonal_fourier_quadratic_fourier
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : Fin n → kˣ) (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.quadraticOperator ψ (diagonal fun i => (a i).val)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val)) x =
      DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a * ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) *
        FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
          (FunctionsMetaplectic.Construction.quadraticOperator ψ (-diagonal fun i => (a i).val⁻¹) f.val)
            (fun i => x i / (a i).val) := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hNondiscrete
  let : (FunctionsMetaplectic.Construction.selfDualMeasure k ψ).IsAddHaarMeasure :=
    NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
  let μ := FunctionsMetaplectic.Construction.positionMeasure k n ψ
  let : μ.IsAddHaarMeasure := by dsimp [μ, FunctionsMetaplectic.Construction.positionMeasure]; infer_instance
  let g : FunctionsMetaplectic.Construction.schwartzBruhat k n := ⟨fun z => f.val z * ψ (-FunctionsMetaplectic.Construction.dot (fun i => x i / (a i).val) z),
    NormalizedFresnel.Construction.nonarchimedean_modulation_mem ψ hu hc f (fun i => x i / (a i).val)⟩
  have hpair := DiagonalQuadratic.Construction.nonarchimedean_diagonal_fresnel_pairing hNondiscrete ψ hu hc hn a g
  have hmod : (∫ y, g.val y * ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) y) ∂μ) =
      FunctionsMetaplectic.Construction.fourierIntegral ψ μ (FunctionsMetaplectic.Construction.quadraticOperator ψ (-diagonal fun i => (a i).val⁻¹) f.val)
        (fun i => x i / (a i).val) := by
    unfold FunctionsMetaplectic.Construction.fourierIntegral
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      change (f.val y * ψ (-FunctionsMetaplectic.Construction.dot (fun i => x i / (a i).val) y)) *
        ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) y) =
        (ψ (FunctionsMetaplectic.Construction.quadratic (-diagonal fun i => (a i).val⁻¹) y) * f.val y) *
          ψ (-FunctionsMetaplectic.Construction.dot (fun i => x i / (a i).val) y)
      rw [FunctionsMetaplectic.Construction.quadratic_neg]
      ring
  rw [diagonal_fourier_quadratic_shift ψ μ a, hpair, hmod]
  ring

end

section

/-! The normalized diagonal Fourier relation on the actual Bruhat space. -/

open _root_.Matrix _root_.MeasureTheory

theorem nonarchimedean_diagonal_fourier_quadratic_relation
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : Fin n → kˣ) (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hwπ : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hw : ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) x, (w.val.2 f).val x =
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    let T := (LinearIntertwiner.Construction.linearOscillator ψ (DiagonalAlgebra.Construction.diagonalGeneralLinear a)).val.2 * w.val.2
    let P := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc)
      (diagonal fun i => (a i).val⁻¹)
    T (P (T f)) = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) • P.symm (T (P.symm f)) := by
  let D := DiagonalAlgebra.Construction.diagonalGeneralLinear a
  let L := (LinearIntertwiner.Construction.linearOscillator ψ D).val.2
  let Li := (LinearIntertwiner.Construction.linearOscillator ψ D⁻¹).val.2
  let F := w.val.2
  let P := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (diagonal fun i => (a i).val⁻¹)
  let Q := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (diagonal fun i => (a i).val)
  have hPL (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : P (L g) = L (Q g) := by
    apply Subtype.ext
    funext x
    change ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) *
      ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 g).val x = ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 (Q g)).val x
    rw [LinearIntertwiner.Construction.linearOscillator_apply, LinearIntertwiner.Construction.linearOscillator_apply]
    change _ = ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k D)))⁻¹ : ℂ) *
      (ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (D⁻¹.val *ᵥ x)) * g.val (D⁻¹.val *ᵥ x))
    rw [DiagonalAlgebra.Construction.diagonalGeneralLinear_inverse_mulVec, DiagonalAlgebra.Construction.diagonal_quadratic_inverse_substitution]
    ring
  have hFL (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : F (L g) = Li (F g) := by
    let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
    let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hNondiscrete ψ hu hc hn
    have he := SymmetricSquareLift.Construction.fourierOscillator_linear_symmetric ψ μ w hwπ hw D (isSymm_diagonal _)
    exact congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator k n ψ => b.val.2 g) he
  have hLL (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : L (Li g) = g := by
    have he := LinearOscillatorHom.Construction.linearOscillator_mul ψ D D⁻¹
    rw [mul_inv_cancel, LinearOscillatorHom.Construction.linearOscillator_one] at he
    exact congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator k n ψ => b.val.2 g) he.symm
  change L (F (P (L (F f)))) = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) • P.symm (L (F (P.symm f)))
  rw [hPL, hFL, hLL]
  have hF (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (F g).val = FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) g.val :=
    funext (hw g)
  have hQ (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (Q g).val = FunctionsMetaplectic.Construction.quadraticOperator ψ (diagonal fun i => (a i).val) g.val := rfl
  have hP (g : FunctionsMetaplectic.Construction.schwartzBruhat k n) : (P.symm g).val =
      FunctionsMetaplectic.Construction.quadraticOperator ψ (-diagonal fun i => (a i).val⁻¹) g.val := rfl
  apply Subtype.ext
  change (F (Q (F f))).val =
    (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) • (P.symm (L (F (P.symm f)))).val
  rw [hF, hQ, hF, hP]
  funext x
  change _ = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) *
    (ψ (FunctionsMetaplectic.Construction.quadratic (-diagonal fun i => (a i).val⁻¹) x) *
      ((LinearIntertwiner.Construction.linearOscillator ψ D).val.2 (F (P.symm f))).val x)
  rw [LinearIntertwiner.Construction.linearOscillator_apply, DiagonalAlgebra.Construction.diagonalGeneralLinear_inverse_mulVec, hF, hP, FunctionsMetaplectic.Construction.quadratic_neg,
    nonarchimedean_diagonal_fourier_quadratic_fourier hNondiscrete ψ hu hc hn,
    DiagonalAlgebra.Construction.diagonalGaussianCoefficient_eq]
  ring

end

/-! Actual bare lifts of diagonal Levi–Weyl products, with prescribed Gaussian phases. -/

open _root_.Matrix

theorem diagonal_levi_quadratic_conjugation {k : Type} [Field k] {n : ℕ} (a : Fin n → kˣ) :
    (Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a))⁻¹ *
      Generators.Construction.quadraticSymplectic ⟨-diagonal (fun i => (a i).val⁻¹), (isSymm_diagonal _).neg⟩ *
      Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a) =
        Generators.Construction.quadraticSymplectic ⟨-diagonal (fun i => (a i).val), (isSymm_diagonal _).neg⟩ := by
  have hcomm : Generators.Construction.quadraticSymplectic (k := k)
      ⟨-diagonal (fun i => (a i).val⁻¹), (isSymm_diagonal _).neg⟩ *
        Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a) =
      Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a) *
        Generators.Construction.quadraticSymplectic ⟨-diagonal (fun i => (a i).val), (isSymm_diagonal _).neg⟩ := by
    apply Subtype.ext
    change fromBlocks 1 0 (-diagonal fun i => (a i).val⁻¹) 1 *
      (Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a)).val =
      (Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a)).val * fromBlocks 1 0 (-diagonal fun i => (a i).val) 1
    rw [Generators.Construction.leviSymplectic_matrix]
    change fromBlocks 1 0 (-diagonal fun i => (a i).val⁻¹) 1 *
      fromBlocks (diagonal fun i => (a i).val) 0 0 (diagonal fun i => ((a i)⁻¹).val)ᵀ =
      fromBlocks (diagonal fun i => (a i).val) 0 0 (diagonal fun i => ((a i)⁻¹).val)ᵀ *
        fromBlocks 1 0 (-diagonal fun i => (a i).val) 1
    rw [diagonal_transpose, fromBlocks_multiply, fromBlocks_multiply]
    simp only [mul_one, one_mul, mul_zero, zero_mul, add_zero, zero_add,
      neg_mul, mul_neg, neg_zero, Units.val_inv_eq_inv_val]
  rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]

theorem exists_nonarchimedean_diagonal_weyl_metaplectic
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k]
    (hNondiscrete : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
    (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
    (a : Fin n → kˣ) (w : FunctionsMetaplectic.Construction.Oscillator k n ψ)
    (hwπ : OscillatorProjection.Construction.oscillatorProjection k n ψ w = Generators.Construction.weylSymplectic k n)
    (hw : ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) x, (w.val.2 f).val x =
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x) :
    ∃ v : FunctionsMetaplectic.Construction.Metaplectic k n ψ,
      FunctionsMetaplectic.Construction.metaplecticProjection k n ψ v = Generators.Construction.leviSymplectic (DiagonalAlgebra.Construction.diagonalGeneralLinear a) * Generators.Construction.weylSymplectic k n ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        FunctionsMetaplectic.Construction.weilRepresentation k n ψ v f = (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val)⁻¹ •
          (LinearIntertwiner.Construction.linearOscillator ψ (DiagonalAlgebra.Construction.diagonalGeneralLinear a)).val.2 (w.val.2 f) := by
  let D := DiagonalAlgebra.Construction.diagonalGeneralLinear a
  let l := LinearIntertwiner.Construction.linearOscillator ψ D
  let t := l * w
  let B : FunctionsMetaplectic.Construction.SymmetricMatrix k n := ⟨diagonal (fun i => (a i).val⁻¹), isSymm_diagonal _⟩
  let u := NonarchimedeanTestSpace.Construction.nonarchimedeanQuadraticMetaplectic hNondiscrete ψ hu hc ⟨-B.val, B.property.neg⟩
  have hconj : t⁻¹ * u.val * t ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ := by
    have h := (inferInstance : (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).Normal).conj_mem u.val u.property t⁻¹
    simpa only [inv_inv] using h
  let v : FunctionsMetaplectic.Construction.Metaplectic k n ψ := ⟨u.val * (t⁻¹ * u.val * t) * u.val,
    (FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem
      ((FunctionsMetaplectic.Construction.metaplecticSubgroup k n ψ).mul_mem u.property hconj) u.property⟩
  have huπ : OscillatorProjection.Construction.oscillatorProjection k n ψ u.val = Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ := rfl
  have hlπ : OscillatorProjection.Construction.oscillatorProjection k n ψ l = Generators.Construction.leviSymplectic D := rfl
  have hupper : OscillatorProjection.Construction.oscillatorProjection k n ψ (t⁻¹ * u.val * t) =
      GenerationSymplectic.Construction.upperSymplectic ⟨diagonal (fun i => (a i).val), isSymm_diagonal _⟩ := by
    calc
      _ = (Generators.Construction.weylSymplectic k n)⁻¹ *
          ((Generators.Construction.leviSymplectic D)⁻¹ * Generators.Construction.quadraticSymplectic ⟨-B.val, B.property.neg⟩ * Generators.Construction.leviSymplectic D) *
          Generators.Construction.weylSymplectic k n := by
        simp only [t, map_mul, map_inv, hlπ, hwπ, huπ, _root_.mul_inv_rev]
        group
      _ = _ := by
        rw [diagonal_levi_quadratic_conjugation]
        exact (OscillatorProjection.Construction.upper_quadratic_conjugation k n ⟨diagonal (fun i => (a i).val), isSymm_diagonal _⟩).symm
  refine ⟨v, ?_, ?_⟩
  · change OscillatorProjection.Construction.oscillatorProjection k n ψ (u.val * (t⁻¹ * u.val * t) * u.val) = _
    rw [map_mul, map_mul, huπ, hupper]
    simpa only [Units.val_inv_eq_inv_val] using DiagonalAlgebra.Construction.diagonal_weyl_factorization a
  · let P := QuadraticIntertwiner.Construction.testQuadratic ψ (NonarchimedeanTestSpace.Construction.nonarchimedean_quadratic_mem ψ hu hc) (diagonal fun i => (a i).val⁻¹)
    have hN : u.val.val.2 = P.symm := by apply LinearEquiv.ext; intro f; rfl
    have hΓ : (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      exact FunctionsMetaplectic.Construction.phase_ne_zero (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hNondiscrete ψ hu hc hn (a i).val (a i).ne_zero).2
    have hword := NormalizedFresnel.Construction.linearEquiv_weyl_word t.val.2 P (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) hΓ
      (nonarchimedean_diagonal_fourier_quadratic_relation hNondiscrete ψ hu hc hn a w hwπ hw)
    intro f
    have hop : FunctionsMetaplectic.Construction.weilRepresentation k n ψ v f = P.symm (t.val.2.symm (P.symm (t.val.2 (P.symm f)))) := by
      change ((u.val.val.2 * ((t.val.2)⁻¹ * u.val.val.2 * t.val.2)) * u.val.val.2) f = _
      rw [hN]
      rfl
    rw [hop, hword]
    rfl

end

end OAI.RepresentationTheory.Weil.Local.NonarchimedeanDiagonalLift.Construction
