import OAI.AlgebraicGeometry.PELModuli.CMPoints.Models
import OAI.AlgebraicGeometry.ComplexMultiplication.CM.ImaginaryElement

/-! # Rational Negative Line -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalNegativeLine

noncomputable section

/-! A complex embedding of a CM field has dense image. Thus each
genuine Hermitian ball, including those with a different rational
Hermitian form on another component, contains a rational negative line. -/

open scoped Classical

theorem cmEmbedding_denseRange {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] (σ : E →ₐ[ℚ] ℂ) : DenseRange σ := by
  obtain ⟨a, ha⟩ := ComplexMultiplication.CM.TypeHodgeStructure.CMEmbeddingType.exists_positive_im σ
  let F : ℝ × ℝ → ℂ := fun t => (t.1 : ℂ) + (t.2 : ℂ) * σ a
  have hF : Continuous F := by fun_prop
  have hs : Function.Surjective F := by
    intro z
    refine ⟨(z.re - z.im / (σ a).im * (σ a).re, z.im / (σ a).im), ?_⟩
    apply Complex.ext
    · simp [F, Complex.mul_re]
    · simp only [F, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, zero_mul, add_zero, zero_add]
      exact div_mul_cancel₀ _ ha.ne'
  have hrat : DenseRange (fun x : ℚ × ℚ => ((x.1 : ℝ), (x.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hd := hs.denseRange.comp hrat hF
  apply hd.mono
  rintro _ ⟨x, rfl⟩
  refine ⟨algebraMap ℚ E x.1 + algebraMap ℚ E x.2 * a, ?_⟩
  simp [F, map_add, map_mul]

theorem exists_rational_negative_vector {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    [NumberField.IsCMField E] (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (w : Fin 3 → ℂ)
    (hw : (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H w w).re < 0) :
    ∃ v : Fin 3 → E, v ≠ 0 ∧
      (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H
        (fun i => σ (v i)) (fun i => σ (v i))).re < 0 := by
  let U : Set (Fin 3 → ℂ) :=
    {x | (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian σ.toRingHom H x x).re < 0}
  have hopen : IsOpen U := by
    apply isOpen_lt _ continuous_const
    unfold AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian
    fun_prop
  have hd : DenseRange (fun v : Fin 3 → E => fun i => σ (v i)) :=
    DenseRange.piMap (fun _ : Fin 3 => cmEmbedding_denseRange σ)
  obtain ⟨v, hv⟩ := hd.exists_mem_open hopen ⟨w, hw⟩
  refine ⟨v, ?_, hv⟩
  intro hzero
  subst v
  simp [U, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian] at hv

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.RationalNegativeLine
