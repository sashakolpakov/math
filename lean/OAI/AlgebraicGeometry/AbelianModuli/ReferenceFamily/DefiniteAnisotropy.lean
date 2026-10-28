import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ComponentUniformization
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

/-! # Definite Anisotropy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteAnisotropy

noncomputable section

/-! A definite complex embedding of a Hermitian matrix excludes every
nonzero isotropic vector over the original number field. -/

open OAI.AlgebraicGeometry.ComplexMultiplication.CM.TraceForm

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]

theorem matrixHermitian_embedding (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (x y : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E) :
    σ (Datum.RankThreePELDatum.matrixHermitian H x y) =
      Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H (fun i => σ (x i)) (fun i => σ (y i)) := by
  unfold Datum.RankThreePELDatum.matrixHermitian Datum.RankThreePELDatum.complexMatrixHermitian
  simp only [map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : ℂ => σ (x i) * σ (H i j) * z) (ComplexMultiplication.CM.TraceForm.cmFieldConjugation_embedding E σ (y j))

theorem matrixHermitian_anisotropic_of_definite (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hdef : (∀ x : Fin 3 → ℂ, x ≠ 0 →
      0 < (Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H x x).re) ∨
      (∀ x : Fin 3 → ℂ, x ≠ 0 →
        (Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H x x).re < 0)) :
    ∀ x : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.VE E, Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0 := by
  intro x hx
  by_contra hn
  have hcn : (fun i => σ (x i)) ≠ 0 := by
    intro h
    apply hn
    ext i
    exact σ.injective ((congrFun h i).trans (map_zero σ).symm)
  have hz : Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H
      (fun i => σ (x i)) (fun i => σ (x i)) = 0 :=
    (matrixHermitian_embedding σ H x x).symm.trans ((congrArg σ hx).trans (map_zero σ))
  rcases hdef with hp | hm
  · have h := hp _ hcn
    rw [hz] at h
    exact lt_irrefl 0 h
  · have h := hm _ hcn
    rw [hz] at h
    exact lt_irrefl 0 h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.DefiniteAnisotropy
