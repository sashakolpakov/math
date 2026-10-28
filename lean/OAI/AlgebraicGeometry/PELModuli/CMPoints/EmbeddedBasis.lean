import OAI.AlgebraicGeometry.PELModuli.CMPoints.HermitianDiagonalization

/-! # Embedded Basis -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddedBasis

noncomputable section

section

/-! Rational coordinate changes remain genuine invertible coordinate
changes at each complex embedding. These explicit maps identify the
orthogonal rational lines with the CM embedding coordinates. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E]

def mapCoordinateEquiv (σ : E →+* ℂ) (e : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  LinearEquiv.ofBijective (Matrix.toLin' (σ.mapMatrix (LinearMap.toMatrix' e.toLinearMap)))
    ((Module.End.isUnit_iff _).mp (Matrix.isUnit_toLin'_iff.mpr
      (((LinearMap.isUnit_toMatrix'_iff).mpr ((Module.End.isUnit_iff _).mpr e.bijective)).map
        σ.mapMatrix)))

def embeddedBasisEquiv (σ : E →+* ℂ) (b : Basis (Fin 3) E (Fin 3 → E)) :
    (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ) :=
  mapCoordinateEquiv σ b.equivFun.symm

theorem embeddedBasisEquiv_apply (σ : E →+* ℂ) (b : Basis (Fin 3) E (Fin 3 → E))
    (x : Fin 3 → ℂ) (i : Fin 3) :
    embeddedBasisEquiv σ b x i = ∑ j, σ (b j i) * x j := by
  change ∑ j, σ ((LinearMap.toMatrix' b.equivFun.symm.toLinearMap) i j) * x j = _
  apply Finset.sum_congr rfl
  intro j _
  have hcol : b.equivFun.symm (Pi.single j 1) = b j := by
    rw [Basis.equivFun_symm_apply]
    simp [Pi.single_apply]
  change σ (b.equivFun.symm (Pi.single j 1) i) * x j = _
  rw [hcol]

theorem embeddedBasisEquiv_eq_sum (σ : E →+* ℂ) (b : Basis (Fin 3) E (Fin 3 → E))
    (x : Fin 3 → ℂ) :
    embeddedBasisEquiv σ b x = ∑ j, x j • (fun i => σ (b j i)) := by
  ext i
  simp [embeddedBasisEquiv_apply, mul_comm]

theorem embeddedBasisEquiv_single (σ : E →+* ℂ) (b : Basis (Fin 3) E (Fin 3 → E))
    (j : Fin 3) :
    embeddedBasisEquiv σ b (Pi.single j 1) = (fun i => σ (b j i)) := by
  ext i
  simp [embeddedBasisEquiv_apply, Pi.single_apply]

theorem embeddedBasisEquiv_rational (σ : E →+* ℂ) (b : Basis (Fin 3) E (Fin 3 → E))
    (x : Fin 3 → E) :
    embeddedBasisEquiv σ b (fun j => σ (x j)) = (fun i => σ (b.equivFun.symm x i)) := by
  ext i
  simp [embeddedBasisEquiv_apply, Basis.equivFun_symm_apply, mul_comm]

variable [Algebra ℚ E]

theorem embeddedBasisEquiv_conjugate (σ : E →ₐ[ℚ] ℂ) (b : Basis (Fin 3) E (Fin 3 → E))
    (x : Fin 3 → ℂ) :
    embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom b (star x) =
      star (embeddedBasisEquiv σ.toRingHom b x) := by
  ext i
  simp [embeddedBasisEquiv_apply, ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding]

end

/-! The bilinear pairing between conjugate embedding spaces is diagonal
in an actual rational orthogonal basis. -/

open scoped Classical

open _root_.Module

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E]

theorem embedding_basis_pairing (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (b : Basis (Fin 3) E (Fin 3 → E)) (i j : Fin 3) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) H () (fun k => σ (b i k))
      (fun k => ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ (b j k)) = σ (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j)) := by
  rw [HermitianDiagonalization.matrixHermitian_embedding]
  rfl

theorem orthogonal_embedding_pairing (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (i : Fin 3) (y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) H () (fun k => σ (b i k))
      (embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom b y) =
        σ (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b i)) * y i := by
  rw [← Geometry.ComplexBall.PrescribedSignsB.matrixB_apply, embeddedBasisEquiv_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]
  have hp (j : Fin 3) :
      Geometry.ComplexBall.PrescribedSignsB.matrixB (fun _ : Unit => σ) H () (fun k => σ (b i k))
        (fun k => (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom (b j k)) =
          σ (AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j)) :=
    (Geometry.ComplexBall.PrescribedSignsB.matrixB_apply _ _ _ _ _).trans (embedding_basis_pairing σ H b i j)
  simp_rw [hp]
  rw [Finset.sum_eq_single i]
  · exact mul_comm _ _
  · intro j _ hji
    rw [hb hji.symm, map_zero, mul_zero]
  · simp

theorem orthogonal_embedding_annihilator (σ : E →ₐ[ℚ] ℂ) (H : Matrix (Fin 3) (Fin 3) E)
    (hani : ∀ x : Fin 3 → E, AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H x x = 0 → x = 0)
    (b : Basis (Fin 3) E (Fin 3 → E))
    (hb : Pairwise (fun i j => AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum.matrixHermitian H (b i) (b j) = 0))
    (i : Fin 3) (y : Geometry.ComplexBall.PrescribedSignsB.Vec) :
    Geometry.ComplexBall.PrescribedSignsB.localB (fun _ : Unit => σ) H () (fun k => σ (b i k))
      (embeddedBasisEquiv (ComplexMultiplication.EmbeddingHodgeType.CM.conjugateEmbedding σ).toRingHom b y) = 0 ↔ y i = 0 := by
  rw [orthogonal_embedding_pairing σ H b hb]
  exact mul_eq_zero.trans (or_iff_right
    (fun hz => HermitianDiagonalization.matrixHermitian_diagonal_ne_zero H hani b i ((map_eq_zero σ).mp hz)))

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddedBasis
