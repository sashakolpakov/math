import OAI.RepresentationTheory.Weil.Local.RealReflectionLift
import OAI.RepresentationTheory.Weil.Local.SquareDeterminantLift

/-! # Real Levi -/

namespace OAI.RepresentationTheory.Weil.Local.RealLevi.Construction

noncomputable section

section

/-! The Gaussian phase for real determinant signs and the single-coordinate reflection. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology Classical

theorem gaussianIndex_real_positive_argument (c : ℝ) (hc : c ≠ 0) (r : ℝ) (hr : 0 < r) :
    FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) r = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 := by
  let b : ℝˣ := Units.mk0 (Real.sqrt r) (Real.sqrt_pos.mpr hr).ne'
  have hlim : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℝ (Gaussian.Construction.realCharacter c) 1) (𝓝[>] (0 : ℝ))
      (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℝ (Gaussian.Construction.realCharacter c) 1)) := by
    rw [Gaussian.Construction.gaussianIntegral_real_eq c 1 hc one_ne_zero]
    exact Gaussian.Construction.regularizedGaussian_real_tendsto c 1 hc one_ne_zero
  have h := SquareDeterminantLift.Construction.gaussianIndex_square_mul_of_limit (Gaussian.Construction.realCharacter c) 1 b hlim
  simpa only [b, Units.val_mk0, Real.sq_sqrt hr.le, one_mul] using h

theorem gaussianIndex_real_negative_argument (c : ℝ) (hc : c ≠ 0) (r : ℝ) (hr : r < 0) :
    FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) r = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) := by
  let b : ℝˣ := Units.mk0 (Real.sqrt (-r)) (Real.sqrt_pos.mpr (neg_pos.mpr hr)).ne'
  have hlim : Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℝ (Gaussian.Construction.realCharacter c) (-1)) (𝓝[>] (0 : ℝ))
      (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℝ (Gaussian.Construction.realCharacter c) (-1))) := by
    rw [Gaussian.Construction.gaussianIntegral_real_eq c (-1) hc (by norm_num)]
    exact Gaussian.Construction.regularizedGaussian_real_tendsto c (-1) hc (by norm_num)
  have h := SquareDeterminantLift.Construction.gaussianIndex_square_mul_of_limit (Gaussian.Construction.realCharacter c) (-1) b hlim
  simpa only [b, Units.val_mk0, Real.sq_sqrt (neg_nonneg.mpr hr.le), neg_mul_neg, one_mul] using h

theorem exists_real_single_reflection_metaplectic {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (j : Fin n) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic ℝ n (Gaussian.Construction.realCharacter c),
      FunctionsMetaplectic.Construction.metaplecticProjection ℝ n (Gaussian.Construction.realCharacter c) m = Generators.Construction.leviSymplectic (SpecialLinearCommutators.Construction.coordinateDiagonal j (-1 : ℝˣ)) ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n,
        FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) m f =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1) •
            (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (SpecialLinearCommutators.Construction.coordinateDiagonal j (-1 : ℝˣ))).val.2 f := by
  let a : Fin n → ℝ := fun i => if i = j then -1 else 1
  have ha (i : Fin n) : a i ^ 2 = 1 := by dsimp [a]; split_ifs <;> norm_num
  have hD : ReflectionAlgebra.Construction.diagonalReflection a ha = SpecialLinearCommutators.Construction.coordinateDiagonal j (-1 : ℝˣ) := Units.ext rfl
  obtain ⟨m, hm, hop⟩ := RealReflectionLift.Construction.exists_real_diagonal_reflection_metaplectic c hc a ha
  rw [hD] at hm
  have hγ : FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ≠ 0 := by
    intro h
    have hn := Gaussian.Construction.gaussianIndex_real_norm c 1 hc one_ne_zero
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  have hratio : (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ^ n =
      FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 := by
    have he (i : Fin n) : FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 =
        if i = j then FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 else 1 := by
      dsimp [a]
      split_ifs
      · rfl
      · exact div_self hγ
    calc
      _ = ∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 := by
        rw [Finset.prod_div_distrib]
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = _ := by simp only [he, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  refine ⟨m, hm, fun f => ?_⟩
  apply Subtype.ext
  funext x
  rw [hop, hratio]
  change _ = (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1) *
    ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) (SpecialLinearCommutators.Construction.coordinateDiagonal j (-1 : ℝˣ))).val.2 f).val x
  rw [← hD, ReflectionAlgebra.Construction.linearOscillator_diagonalReflection_apply]

end

/-! The exact bare Levi generator over the real field for every determinant. -/

open _root_.Matrix

theorem exists_real_levi_metaplectic
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) :
    ∃ m : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ, FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ m = Generators.Construction.leviSymplectic A ∧
      ∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
        (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ m f).val x =
          (FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ (FunctionsMetaplectic.Construction.determinantUnit ℝ A) / FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ 1) *
            ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus ℝ (FunctionsMetaplectic.Construction.determinantUnit ℝ A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) := by
  by_cases hA : 0 < A.val.det
  · exact SquareDeterminantLift.Construction.exists_real_positive_det_levi_metaplectic hn ψ hc hu hψ A hA
  obtain ⟨c, hc0, rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hψ
  have hAdet : A.val.det ≠ 0 := (FunctionsMetaplectic.Construction.determinantUnit ℝ A).ne_zero
  have hAneg : A.val.det < 0 := lt_of_le_of_ne (le_of_not_gt hA) hAdet
  let j : Fin n := ⟨0, hn⟩
  let D := SpecialLinearCommutators.Construction.coordinateDiagonal j (-1 : ℝˣ)
  have hDD : D * D = 1 := by
    rw [show D * D = SpecialLinearCommutators.Construction.coordinateDiagonal j ((-1 : ℝˣ) ^ 2) from SquareDeterminantLift.Construction.coordinateDiagonal_square j (-1)]
    apply Units.ext
    norm_num [SpecialLinearCommutators.Construction.coordinateDiagonal]
  have hDdet : D.val.det = -1 := by
    change (FunctionsMetaplectic.Construction.determinantUnit ℝ D).val = -1
    rw [ComplexLevi.Construction.coordinateDiagonal_determinant]
    rfl
  let S := A * D
  have hSpos : 0 < S.val.det := by
    change 0 < (A.val * D.val).det
    rw [Matrix.det_mul, hDdet, mul_neg_one]
    exact neg_pos.mpr hAneg
  have hSD : S * D = A := by dsimp [S]; rw [mul_assoc, hDD, mul_one]
  obtain ⟨mS, hmS, hmSa⟩ := SquareDeterminantLift.Construction.exists_real_positive_det_levi_metaplectic hn (Gaussian.Construction.realCharacter c) hc hu hψ S hSpos
  obtain ⟨mD, hmD, hmDa⟩ := exists_real_single_reflection_metaplectic c hc0 j
  have hγ0 : FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 ≠ 0 := by
    intro h
    have hh := Gaussian.Construction.gaussianIndex_real_norm c 1 hc0 one_ne_zero
    rw [h, norm_zero] at hh
    exact zero_ne_one hh
  have hγS : FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.determinantUnit ℝ S) = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1 :=
    gaussianIndex_real_positive_argument c hc0 S.val.det hSpos
  have hγA : FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.determinantUnit ℝ A) = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) :=
    gaussianIndex_real_negative_argument c hc0 A.val.det hAneg
  have hmSop (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
      FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) mS f = (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) S).val.2 f := by
    apply Subtype.ext
    funext x
    rw [hmSa, hγS, div_self hγ0, one_mul]
    exact (LinearIntertwiner.Construction.linearOscillator_apply (Gaussian.Construction.realCharacter c) S f x).symm
  have hL : LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) S * LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) D =
      LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) A := by rw [← LinearOscillatorHom.Construction.linearOscillator_mul, hSD]
  refine ⟨mS * mD, ?_, fun f x => ?_⟩
  · rw [map_mul, hmS, hmD]
    exact congrArg (OscillatorProjection.Construction.oscillatorProjection ℝ n (Gaussian.Construction.realCharacter c)) hL
  · change (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) mS (FunctionsMetaplectic.Construction.weilRepresentation ℝ n (Gaussian.Construction.realCharacter c) mD f)).val x = _
    rw [hmSop, hmDa, map_smul]
    have he := congrArg (fun b : FunctionsMetaplectic.Construction.Oscillator ℝ n (Gaussian.Construction.realCharacter c) => b.val.2 f) hL
    change (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) S).val.2 ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) D).val.2 f) =
      (LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) A).val.2 f at he
    change (FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (-1) / FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) 1) *
      ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) S).val.2 ((LinearIntertwiner.Construction.linearOscillator (Gaussian.Construction.realCharacter c) D).val.2 f)).val x = _
    rw [he, LinearIntertwiner.Construction.linearOscillator_apply, hγA]
    ring

def realLinearMetaplectic
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) : FunctionsMetaplectic.Construction.Metaplectic ℝ n ψ :=
  Classical.choose (exists_real_levi_metaplectic n hn ψ hc hu hψ A)

theorem realLinearMetaplectic_projection
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n) :
    FunctionsMetaplectic.Construction.metaplecticProjection ℝ n ψ (realLinearMetaplectic n hn ψ hc hu hψ A) = Generators.Construction.leviSymplectic A :=
  (Classical.choose_spec (exists_real_levi_metaplectic n hn ψ hc hu hψ A)).1

theorem realLinearMetaplectic_apply
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1) (A : FunctionsMetaplectic.Construction.GeneralLinear ℝ n)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    (FunctionsMetaplectic.Construction.weilRepresentation ℝ n ψ (realLinearMetaplectic n hn ψ hc hu hψ A) f).val x =
      (FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ (FunctionsMetaplectic.Construction.determinantUnit ℝ A) / FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ 1) *
        ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus ℝ (FunctionsMetaplectic.Construction.determinantUnit ℝ A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) :=
  (Classical.choose_spec (exists_real_levi_metaplectic n hn ψ hc hu hψ A)).2 f x

end

end OAI.RepresentationTheory.Weil.Local.RealLevi.Construction
