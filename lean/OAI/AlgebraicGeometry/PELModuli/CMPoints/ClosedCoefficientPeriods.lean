import OAI.AlgebraicGeometry.PELModuli.CMPoints.BasisHodge
import OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddedBasis
import OAI.AlgebraicGeometry.PELModuli.CMPoints.ZeroPeriod

/-! # Closed Coefficient Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods

noncomputable section

section

/-! The CM decomposition in an orthogonal rational basis has exactly
the negative-line and annihilator subspaces of the component period. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}
  (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

def componentPrescribed (H : Matrix (Fin 3) (Fin 3) E) (v : Geometry.ComplexBall.PrescribedSignsB.Vec)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) : Prop :=
  ∀ i, if i = P.distinguished then
    (u i).1 ∈ Submodule.span ℂ {v} ∧ Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings H i v (u i).2 = 0
  else if P.compactSigns i then (u i).1 = 0 else (u i).2 = 0

omit [NumberField E] [NumberField.IsCMField E] [Algebra ℚ E] in
theorem embeddedBasis_line_mem (σ : E →+* ℂ) (b : Basis (Fin 3) E (Fin 3 → E))
    (x : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    EmbeddedBasis.embeddedBasisEquiv σ b x ∈ Submodule.span ℂ {fun i => σ (b 2 i)} ↔
      x ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)} := by
  have hs : EmbeddedBasis.embeddedBasisEquiv σ b (Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)) = (fun i => σ (b 2 i)) := by
    ext i
    simp [EmbeddedBasis.embeddedBasisEquiv_apply, Geometry.ComplexBall.PrescribedSignsB.lineVector, Fin.sum_univ_succ]
  rw [← hs, Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, (EmbeddedBasis.embeddedBasisEquiv σ b).injective ((map_smul _ _ _).trans ha)⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, (map_smul _ _ _).symm⟩

include hP in
theorem coordinateSignCondition_iff_componentPrescribed
    (H : Matrix (Fin 3) (Fin 3) E)
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    PeriodCoordinates.coordinateSignCondition P u ↔
      componentPrescribed P H (fun i => P.μ (b 2 i)) (BasisHodge.ambientBasisEquiv P b u) := by
  rw [ZeroPeriod.zero_signCondition_iff_prescribed P hP]
  unfold Geometry.ComplexBall.PrescribedSignsB.Prescribed componentPrescribed
  apply forall_congr'
  intro i
  by_cases hi : i = P.distinguished
  · subst i
    simp only [ite_true]
    change ((u P.distinguished).1 ∈ Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (0 : Geometry.ComplexBall.PrescribedSignsB.BallChart)} ∧
      Geometry.ComplexBall.PrescribedSignsB.localB P.embeddings (Matrix.diagonal ![1, 1, P.b]) P.distinguished
        (Geometry.ComplexBall.PrescribedSignsB.lineVector 0) (u P.distinguished).2 = 0) ↔
      (EmbeddedBasis.embeddedBasisEquiv P.μ b (u P.distinguished).1 ∈
        Submodule.span ℂ {fun i => P.μ (b 2 i)} ∧
      Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => P.embeddings P.distinguished) H ()
        (fun i => P.embeddings P.distinguished (b 2 i))
        (EmbeddedBasis.embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings P.distinguished)).toRingHom b
          (u P.distinguished).2) = 0)
    rw [embeddedBasis_line_mem,
      EmbeddedBasis.orthogonal_embedding_annihilator (P.embeddings P.distinguished) H hani b hb 2,
      ZeroPeriod.diagonal_pairing_zero_line]
    have hn : P.embeddings P.distinguished P.b ≠ 0 :=
      (map_ne_zero _).mpr hP.2.2.1
    rw [mul_eq_zero, or_iff_right hn]
  · simp only [hi, ite_false]
    cases hsign : P.compactSigns i
    · change (u i).2 = 0 ↔ EmbeddedBasis.embeddedBasisEquiv
        (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom b (u i).2 = 0
      exact (EmbeddedBasis.embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding (P.embeddings i)).toRingHom b).map_eq_zero_iff.symm
    · change (u i).1 = 0 ↔ EmbeddedBasis.embeddedBasisEquiv (P.embeddings i).toRingHom b (u i).1 = 0
      exact (EmbeddedBasis.embeddedBasisEquiv (P.embeddings i).toRingHom b).map_eq_zero_iff.symm

theorem basisCMHodge_component_period (H : Matrix (Fin 3) (Fin 3) E)
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic ↔
      componentPrescribed P H (fun i => P.μ (b 2 i)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  rw [BasisHodge.basisCMHodge_holomorphic,
    coordinateSignCondition_iff_componentPrescribed P hP H hani b hb,
    LinearEquiv.apply_symm_apply]

end

/-! The exact coefficient-period conditions form a closed relation in
the parameter and normalized ball coordinates. -/

open Set
open scoped Classical

theorem mem_span_normalized_line_iff (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : Geometry.ComplexBall.PrescribedSignsB.BallChart) (x : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    x ∈ Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector z)} ↔
      x = (e.symm x) 2 • e (Geometry.ComplexBall.PrescribedSignsB.lineVector z) := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    have hc : a = e.symm x 2 := by
      have h := congrArg (fun v : Geometry.ComplexBall.PrescribedSignsB.Vec => e.symm v 2) ha
      simpa [Geometry.ComplexBall.PrescribedSignsB.lineVector] using h
    rw [← hc]
    exact ha.symm
  · intro hx
    exact ⟨e.symm x 2, hx.symm⟩

theorem isClosed_mem_normalized_line
    {X : Type*} [TopologicalSpace X]
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (z : X → Geometry.ComplexBall.PrescribedSignsB.BallChart) (x : X → Geometry.ComplexBall.PrescribedSignsB.Vec)
    (hz : Continuous z) (hx : Continuous x) :
    IsClosed {q : X | x q ∈ Submodule.span ℂ {e (Geometry.ComplexBall.PrescribedSignsB.lineVector (z q))}} := by
  simp only [mem_span_normalized_line_iff]
  apply isClosed_eq hx
  exact ((continuous_apply 2).comp (e.symm.continuous_of_finiteDimensional.comp hx)).smul
    (e.continuous_of_finiteDimensional.comp (Geometry.ComplexBall.PrescribedSignsB.lineVector_differentiable.continuous.comp hz))

theorem isClosed_componentPrescribed
    {E X : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    [TopologicalSpace X] {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s)
    (H : Matrix (Fin 3) (Fin 3) E) (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (z : X → Geometry.ComplexBall.PrescribedSignsB.BallChart) (u : X → Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s))
    (hz : Continuous z) (hu : Continuous u) :
    IsClosed {q : X | componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector (z q))) (u q)} := by
  unfold componentPrescribed
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  by_cases hi : i = P.distinguished
  · simp only [hi, ite_true, ofPred_and]
    apply IsClosed.inter
    · exact isClosed_mem_normalized_line e z (fun q => (u q P.distinguished).1) hz
        (((continuous_apply P.distinguished).comp hu).fst)
    · apply isClosed_eq _ continuous_const
      have hline : Continuous (fun q => e (Geometry.ComplexBall.PrescribedSignsB.lineVector (z q))) :=
        e.continuous_of_finiteDimensional.comp (Geometry.ComplexBall.PrescribedSignsB.lineVector_differentiable.continuous.comp hz)
      have hvec : Continuous (fun q => (u q P.distinguished).2) :=
        ((continuous_apply P.distinguished).comp hu).snd
      unfold Geometry.ComplexBall.PrescribedSignsB.localB
      apply continuous_finsetSum
      intro j _
      apply continuous_finsetSum
      intro k _
      exact (((continuous_apply j).comp hline).mul continuous_const).mul
        ((continuous_apply k).comp hvec)
  · simp only [hi, ite_false]
    split_ifs
    · exact isClosed_eq (((continuous_apply i).comp hu).fst) continuous_const
    · exact isClosed_eq (((continuous_apply i).comp hu).snd) continuous_const

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.ClosedCoefficientPeriods
