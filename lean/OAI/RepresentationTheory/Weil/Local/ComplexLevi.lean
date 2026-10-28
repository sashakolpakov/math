import OAI.RepresentationTheory.Weil.Local.SymmetricSquareLift
import OAI.RepresentationTheory.Weil.Local.ComplexCover
import OAI.RepresentationTheory.Weil.Local.SpecialLinearCommutators

/-! # Complex Levi -/

namespace OAI.RepresentationTheory.Weil.Local.ComplexLevi.Construction

noncomputable section

/-! The prescribed bare Levi lifts at the complex place. -/

open _root_.Matrix _root_.MeasureTheory
open scoped Classical

theorem coordinateDiagonal_determinant
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (i : Fin n) (a : kˣ) : FunctionsMetaplectic.Construction.determinantUnit k (SpecialLinearCommutators.Construction.coordinateDiagonal i a) = a := by
  apply Units.ext
  simp [FunctionsMetaplectic.Construction.determinantUnit, SpecialLinearCommutators.Construction.coordinateDiagonal]

theorem coordinateDiagonal_complex_square {n : ℕ} (i : Fin n) (a : ℂˣ) :
    ∃ B : FunctionsMetaplectic.Construction.GeneralLinear ℂ n, B.val.IsSymm ∧ B * B = SpecialLinearCommutators.Construction.coordinateDiagonal i a := by
  let b : ℂ := a.val ^ (1 / 2 : ℂ)
  have hb : b ^ (2 : ℕ) = a.val := by simp [b, one_div]
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide)] at hb
    exact a.ne_zero hb.symm
  let u : ℂˣ := Units.mk0 b hb0
  refine ⟨SpecialLinearCommutators.Construction.coordinateDiagonal i u, Matrix.isSymm_diagonal _, ?_⟩
  apply Units.ext
  change diagonal (fun j => if j = i then b else 1) * diagonal (fun j => if j = i then b else 1) =
    diagonal (fun j => if j = i then a.val else 1)
  rw [diagonal_mul_diagonal]
  congr 1
  funext j
  split_ifs
  · exact (pow_two b).symm.trans hb
  · exact one_mul 1

theorem complex_linearOscillator_mem_metaplectic
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℂ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1)
    (A : FunctionsMetaplectic.Construction.GeneralLinear ℂ n) : LinearIntertwiner.Construction.linearOscillator ψ A ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ := by
  let i : Fin n := ⟨0, hn⟩
  let d := FunctionsMetaplectic.Construction.determinantUnit ℂ A
  let D := SpecialLinearCommutators.Construction.coordinateDiagonal i d
  obtain ⟨B, hB, hBB⟩ := coordinateDiagonal_complex_square i d
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure ℂ ψ
  let : μ.IsAddHaarMeasure := (ComplexCover.Construction.complex_analytic_normalization ψ hc hu hψ n).2.1
  let w := ComplexCover.Construction.complexRawFourierOscillator n ψ hc hu hψ
  have hD : LinearIntertwiner.Construction.linearOscillator ψ D ∈ FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ := by
    rw [show D = B * B from hBB.symm]
    exact SymmetricSquareLift.Construction.linearOscillator_symmetric_square_mem ψ μ w rfl
      (ComplexCover.Construction.complexRawFourierOscillator_apply n ψ hc hu hψ) B hB
  let S := A * D⁻¹
  have hS : S.val.det = 1 := by
    change (FunctionsMetaplectic.Construction.determinantUnit ℂ (A * D⁻¹)).val = 1
    rw [LinearOscillatorHom.Construction.determinantUnit_mul, FourierLinearSubstitution.Construction.determinantUnit_inv]
    have hd : FunctionsMetaplectic.Construction.determinantUnit ℂ D = FunctionsMetaplectic.Construction.determinantUnit ℂ A := coordinateDiagonal_determinant i d
    rw [hd, mul_inv_cancel]
    rfl
  have h := (FunctionsMetaplectic.Construction.metaplecticSubgroup ℂ n ψ).mul_mem (SpecialLinearCommutators.Construction.linearOscillator_mem_of_det_one ψ S hS) hD
  rw [← LinearOscillatorHom.Construction.linearOscillator_mul] at h
  simpa only [S, mul_assoc, inv_mul_cancel, mul_one] using h

def complexLinearMetaplectic
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℂ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1)
    (A : FunctionsMetaplectic.Construction.GeneralLinear ℂ n) : FunctionsMetaplectic.Construction.Metaplectic ℂ n ψ :=
  ⟨LinearIntertwiner.Construction.linearOscillator ψ A, complex_linearOscillator_mem_metaplectic n hn ψ hc hu hψ A⟩

theorem complexLinearMetaplectic_projection
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℂ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1)
    (A : FunctionsMetaplectic.Construction.GeneralLinear ℂ n) :
    FunctionsMetaplectic.Construction.metaplecticProjection ℂ n ψ (complexLinearMetaplectic n hn ψ hc hu hψ A) = Generators.Construction.leviSymplectic A := rfl

theorem complexLinearMetaplectic_apply
    (n : ℕ) (hn : 0 < n) (ψ : AddChar ℂ ℂ)
    (hc : Continuous (fun t => ψ t)) (hu : ∀ t, ‖ψ t‖ = 1) (hψ : ∃ t, ψ t ≠ 1)
    (A : FunctionsMetaplectic.Construction.GeneralLinear ℂ n) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℂ n) (x : FunctionsMetaplectic.Construction.Position ℂ n) :
    (FunctionsMetaplectic.Construction.weilRepresentation ℂ n ψ (complexLinearMetaplectic n hn ψ hc hu hψ A) f).val x =
      (FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ (FunctionsMetaplectic.Construction.determinantUnit ℂ A) / FunctionsMetaplectic.Construction.gaussianIndex ℂ ψ 1) *
      ((Real.sqrt (FunctionsMetaplectic.Construction.localModulus ℂ (FunctionsMetaplectic.Construction.determinantUnit ℂ A)))⁻¹ : ℂ) * f.val (A⁻¹.val *ᵥ x) := by
  have hdet := (ArchimedeanTestSpace.Construction.complex_gaussian_normalization ψ hc hu hψ (FunctionsMetaplectic.Construction.determinantUnit ℂ A).val
    (FunctionsMetaplectic.Construction.determinantUnit ℂ A).ne_zero).2.2
  have hone := (ArchimedeanTestSpace.Construction.complex_gaussian_normalization ψ hc hu hψ 1 one_ne_zero).2.2
  rw [hdet, hone, div_self one_ne_zero, one_mul]
  exact LinearIntertwiner.Construction.linearOscillator_apply ψ A f x

end

end OAI.RepresentationTheory.Weil.Local.ComplexLevi.Construction
