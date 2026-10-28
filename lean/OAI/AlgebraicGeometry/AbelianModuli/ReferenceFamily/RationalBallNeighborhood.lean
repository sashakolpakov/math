import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.BallReflectionLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.ReflectionInterfaces
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalReflectionNormLevel
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.NonisotropicReflectionVector
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.BallRealization

/-! # Rational Ball Neighborhood -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalBallNeighborhood

noncomputable section

/-! Rational Hermitian isometries with the actual lattice congruence
condition meet every neighborhood in the original ReferenceFamily ball coordinates.
The field matrix, complex normalizer, affine action and lattice are the
original objects used by the arithmetic-component specification.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E] [NumberField.IsCMField E]
    {s : ℕ} (P : Datum.RankThreePELDatum E s)

theorem exists_rational_isometry_in_original_ball_neighborhood
    (hP : P.IsAdmissible) (H : Matrix (Fin 3) (Fin 3) E)
    (hHerm : ∀ i j, H i j = NumberField.IsCMField.complexConj E (H j i))
    (hdet : H.det ≠ 0)
    (Λ : Submodule ℤ (Fin 3 → E)) (hΛ : NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice Λ)
    (e : (Fin 3 → ℂ) ≃ₗ[ℂ] (Fin 3 → ℂ))
    (he : ∀ x y, Datum.RankThreePELDatum.complexMatrixHermitian P.μ H (e x) (e y) =
      Datum.RankThreePELDatum.complexMatrixHermitian P.μ (Matrix.diagonal ![1, 1, P.b]) x y)
    (N : ℕ) (hN : 0 < N) (z w : P.Domain)
    (U : Set Geometry.ComplexBall.PrescribedSignsB.BallChart) (hU : IsOpen U) (hwU : w.val ∈ U) :
    ∃ g : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E),
      (∀ x y, Datum.RankThreePELDatum.matrixHermitian H (g x) (g y) =
        Datum.RankThreePELDatum.matrixHermitian H x y) ∧
      LinearMap.det g.toLinearMap = 1 ∧
      LatticeReflectionCongruence.ClearedPrincipalLatticeCongruence Λ N g ∧
      P.lineActionVia e g z.val ∈ U := by
  have hbim : (P.μ P.b).im = 0 := by
    apply Complex.conj_eq_iff_im.mp
    exact (NumberField.IsCMField.complexEmbedding_complexConj E P.μ P.b).symm.trans
      (congrArg P.μ hP.2.1)
  let v (t : P.Domain) := Intrinsic.BallReflectionLifts.nativeBallReflectionLift (P.μ P.b) hbim hP.2.2.2.1
    (P.arithmeticBallEquiv t)
  let x := e (v z)
  let y := e (v w)
  have hnorm (t : P.Domain) :
      MatrixReflectionEmbedding.matrixReflectionForm (starRingEnd ℂ) (H.map P.μ) (e (v t)) (e (v t)) = P.μ P.b := by
    rw [ReflectionInterfaces.complexReflectionForm_eq_original, he, Normalized.HodgeLine.complexMatrixHermitian_diagonal]
    exact Intrinsic.BallReflectionLifts.nativeBallReflectionLift_norm (P.μ P.b) hbim hP.2.2.2.1 (P.arithmeticBallEquiv t)
  have hlast (t : P.Domain) : (e.symm (e (v t))) 2 ≠ 0 := by
    rw [e.symm_apply_apply]
    exact Intrinsic.BallReflectionLifts.nativeBallReflectionLift_last_ne_zero (P.μ P.b) hbim hP.2.2.2.1
      (P.arithmeticBallEquiv t)
  have hcoord (t : P.Domain) : NegativeLine.negativeLineCoordinate (e.symm (e (v t))) = t.val := by
    rw [e.symm_apply_apply]
    exact (Intrinsic.BallReflectionLifts.nativeBallReflectionLift_coordinate (P.μ P.b) hbim hP.2.2.2.1
      (P.arithmeticBallEquiv t)).trans (P.arithmeticBallEquiv_val t)
  have hy : y ∈ NegativeCoordinateOpen.negativeCoordinateOpenPreimage e U := by
    refine ⟨hlast w, ?_⟩
    change NegativeLine.negativeLineCoordinate (e.symm (e (v w))) ∈ U
    rwa [hcoord w]
  have hphase : ∀ a : ℂ, ‖a‖ = 1 → a • y ∈ NegativeCoordinateOpen.negativeCoordinateOpenPreimage e U := by
    intro a ha
    apply NegativeCoordinateOpen.negativeCoordinateOpenPreimage_smul e U y hy a
    intro hzero
    rw [hzero, norm_zero] at ha
    exact zero_ne_one ha
  obtain ⟨r, hr⟩ := NonisotropicReflectionVector.exists_nonisotropic_cm_matrix_vector_of_det P.μ H hdet
  have hΛ' : @NumberTheory.ArithmeticGroups.Data.CongruenceLevel.FullStableLattice E _ DivisionRing.toRatAlgebra Λ := by
    have hA : (inferInstance : Algebra ℚ E) = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
    exact hA ▸ hΛ
  obtain ⟨g, hhit, hpres, hgdet, hcongr⟩ := RationalReflectionNormLevel.exists_rational_lattice_reflections_at_common_norm
    P.μ H hHerm r hr Λ hΛ' N hN P.b hP.2.2.1 hP.2.1 x y (hnorm z) (hnorm w)
      (NegativeCoordinateOpen.negativeCoordinateOpenPreimage e U) (NegativeCoordinateOpen.negativeCoordinateOpenPreimage_isOpen e U hU) hphase
  refine ⟨g, ?_, hgdet, hcongr, ?_⟩
  · intro a d
    simpa only [ReflectionInterfaces.matrixReflectionForm_eq_original] using hpres a d
  · rw [NegativeCoordinateOpen.lineActionVia_eq_on_vector_representative P e g z.val x (hlast z) (hcoord z)]
    exact hhit.2

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.RationalBallNeighborhood
