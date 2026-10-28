import OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalRationalBallPoint
import OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianOrthogonalBasis
import OAI.AlgebraicGeometry.PELModuli.CMPoints.PeriodOnBall

/-! # Local Periods -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPeriods

noncomputable section

/-! Construct a coordinate-CM period in every nonempty open part of any
Hermitian ball with the prescribed signatures. Only the chosen negative
line must be non-null; global anisotropy is unnecessary. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] {s : ℕ}

theorem orthogonal_embedding_annihilator_of_self_ne_zero
    (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (i : Fin 3) (hself : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b i) ≠ 0) (y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) H () (fun k => σ (b i k))
      (EmbeddedBasis.embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom b y) = 0 ↔ y i = 0 := by
  rw [EmbeddedBasis.orthogonal_embedding_pairing σ H b hb]
  exact mul_eq_zero.trans (or_iff_right ((map_ne_zero σ).mpr hself))

variable (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)

include hP in
theorem coordinateSignCondition_iff_componentPrescribed_of_last_ne_zero
    (H : Matrix (Fin 3) (Fin 3) E)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (hself : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b 2) (b 2) ≠ 0)
    (u : Geometry.ComplexBall.PrescribedSignsB.Ambient (Fin s)) :
    PeriodCoordinates.coordinateSignCondition P u ↔
      ClosedCoefficientPeriods.componentPrescribed P H (fun i => P.μ (b 2 i)) (BasisHodge.ambientBasisEquiv P b u) := by
  rw [ZeroPeriod.zero_signCondition_iff_prescribed P hP]
  unfold Geometry.ComplexBall.PrescribedSignsB.Prescribed ClosedCoefficientPeriods.componentPrescribed
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
    rw [ClosedCoefficientPeriods.embeddedBasis_line_mem,
      orthogonal_embedding_annihilator_of_self_ne_zero (P.embeddings P.distinguished) H b hb 2 hself,
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

theorem basisCMHodge_component_period_of_last_ne_zero (H : Matrix (Fin 3) (Fin 3) E)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (hself : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b 2) (b 2) ≠ 0)
    (x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E)) :
    x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic ↔
      ClosedCoefficientPeriods.componentPrescribed P H (fun i => P.μ (b 2 i)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  rw [BasisHodge.basisCMHodge_holomorphic,
    coordinateSignCondition_iff_componentPrescribed_of_last_ne_zero P hP H b hb hself,
    LinearEquiv.apply_symm_apply]

theorem exists_CM_period_in_open
    (H : Matrix (Fin 3) (Fin 3) E)
    (hH : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (e : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (he : ∀ x y, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hU : IsOpen U) (hUd : U ⊆ P.domain) (hUn : U.Nonempty) :
    ∃ (z : P.Domain) (b : Basis (Fin 3) E (Fin 3 → E)), z.val ∈ U ∧
      ∀ x : ComplexMultiplication.WeightOne.CM.Complexification (Fin 3 → E),
        x ∈ (BasisHodge.basisCMHodge P hP b).holomorphic ↔
          ClosedCoefficientPeriods.componentPrescribed P H (e (Geometry.ComplexBall.PrescribedSignsB.lineVector z.val)) (PeriodCoordinates.cmPeriodCoordinates P hP x) := by
  obtain ⟨z, v, a, hzU, _, ha, heq, hv⟩ := LocalRationalBallPoint.exists_rational_ball_line_in_open P H e he U hU hUd hUn
  have hvself : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H v v ≠ 0 := by
    intro h
    have hz := HermitianDiagonalization.matrixHermitian_embedding (P.embeddings P.distinguished) H v v
    rw [h, map_zero] at hz
    change 0 = AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (fun i => P.μ (v i))
      (fun i => P.μ (v i)) at hz
    rw [← hz] at hv
    exact (lt_irrefl 0) hv
  let c := (NumberField.IsCMField.complexConj E).toRingEquiv
  have hc : c P.imaginaryScalar ≠ P.imaginaryScalar := by
    intro h
    have hi : c P.imaginaryScalar = -P.imaginaryScalar := hP.2.2.2.2.2.2.2.1
    have ht : (2 : E) * P.imaginaryScalar = 0 := by
      rw [hi] at h
      linear_combination -h
    exact hP.2.2.2.2.2.2.1 ((mul_eq_zero.mp ht).resolve_left (by norm_num))
  obtain ⟨b, hb0, hb⟩ := HermitianOrthogonalBasis.exists_hermitian_orthogonal_basis_with_first
    c P.imaginaryScalar hc (HermitianDiagonalization.matrixHermitianFirstLinear H)
    (HermitianDiagonalization.matrixHermitian_conjugate_swap H hH) v hvself 2 (by simp)
  let b' := b.reindex (Equiv.swap 0 2)
  have hlast : b' 2 = v := by
    simpa only [b', Basis.reindex_apply, Equiv.symm_swap, Equiv.swap_apply_right] using hb0
  have ho : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b' i) (b' j) = 0) := by
    intro i j hij
    have h := hb ((Equiv.swap (0 : Fin 3) 2).symm.injective.ne hij)
    change AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b ((Equiv.swap (0 : Fin 3) 2).symm i))
      (b ((Equiv.swap (0 : Fin 3) 2).symm j)) = 0 at h
    simpa only [b', Basis.reindex_apply] using h
  have hself : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b' 2) (b' 2) ≠ 0 := by
    simpa only [hlast] using hvself
  refine ⟨z, b', hzU, fun x => ?_⟩
  rw [heq, PeriodOnBall.componentPrescribed_smul P H a ha,
    basisCMHodge_component_period_of_last_ne_zero P hP H b' ho hself, hlast]

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.LocalPeriods
