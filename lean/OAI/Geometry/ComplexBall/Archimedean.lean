import OAI.Geometry.ComplexBall.RealPlaces
import OAI.Geometry.ComplexBall.IntegralLattice

/-! # Archimedean -/

namespace OAI.Geometry.ComplexBall.Archimedean.ArithmeticQuotient

noncomputable section

/-! The distinguished real factor is the original complex matrix group at μ.
The isomorphism is chosen to commute with the specified field embedding. -/

open scoped Classical QuadraticAlgebra
open _root_.NumberField _root_.Topology

def complexUnitaryCoefficientEquiv (b b' : ℂ) (h : b = b') :
    ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b ≃ₜ* ArithmeticQuotientEquationsData.SU (starRingEnd ℂ) b' where
  toMulEquiv := ArithmeticQuotientSplitUnitary.unitaryCoefficientEquiv _ b b' h
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma imaginary_embedding_im_ne_zero (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (μ : E →+* ℂ) : (μ δ).im ≠ 0 := by
  intro him
  apply (map_ne_zero μ).mpr hδ0
  exact Complex.ext (ArithmeticQuotientEquationsData.imaginary_generator_embedding_re δ hδ μ) him

lemma imaginary_embedding_im_sq (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (μ : E →+* ℂ) : (μ δ).im ^ 2 = -RealPlaces.ArithmeticQuotient.realEmbedding μ (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) := by
  change (μ δ).im ^ 2 = -(μ (δ ^ 2)).re
  rw [map_pow]
  simp [pow_two, Complex.mul_re, ArithmeticQuotientEquationsData.imaginary_generator_embedding_re δ hδ μ]

def originalRealPointsEquiv (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ) :
    (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).Points (RealPlaces.ArithmeticQuotient.realEmbedding μ) ≃ₜ* ArithmeticQuotientEquationsData.ArchimedeanSU b μ :=
  (RealPoints.ArithmeticQuotient.realUnitaryPointsContinuousEquiv (RealPlaces.ArithmeticQuotient.realEmbedding μ (ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (μ δ).im
    (RealPlaces.ArithmeticQuotient.realEmbedding μ (ArithmeticQuotientSplitUnitary.realCoefficient b hb)) (imaginary_embedding_im_sq δ hδ μ)
    (imaginary_embedding_im_ne_zero δ hδ hδ0 μ)).trans
      (complexUnitaryCoefficientEquiv _ (μ b) (RealPlaces.ArithmeticQuotient.realEmbedding_coe μ (ArithmeticQuotientSplitUnitary.realCoefficient b hb)))

lemma realQuadraticHom_scalarExtension (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (μ : E →+* ℂ)
    (z : QuadraticAlgebra (ArithmeticQuotientEquationsData.RealField E) (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) 0) :
    RealQuadratic.ArithmeticQuotient.realQuadraticHom (RealPlaces.ArithmeticQuotient.realEmbedding μ (ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (μ δ).im
      (imaginary_embedding_im_sq δ hδ μ)
      (ArithmeticQuotientEquationsData.quadraticMap (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) (RealPlaces.ArithmeticQuotient.realEmbedding μ) z) =
        μ (ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0 z) := by
  rw [RealQuadratic.ArithmeticQuotient.realQuadraticHom_apply]
  change (RealPlaces.ArithmeticQuotient.realEmbedding μ z.re : ℂ) + (RealPlaces.ArithmeticQuotient.realEmbedding μ z.im : ℂ) *
    ((μ δ).im * Complex.I) = μ (ArithmeticQuotientEquationsData.quadraticLift δ hδ z)
  rw [RealPlaces.ArithmeticQuotient.realEmbedding_coe, RealPlaces.ArithmeticQuotient.realEmbedding_coe, ArithmeticQuotientEquationsData.quadraticLift_apply, map_add, map_mul]
  have he : ((μ δ).im : ℂ) * Complex.I = μ δ := by
    apply Complex.ext <;> simp [ArithmeticQuotientEquationsData.imaginary_generator_embedding_re δ hδ μ]
  rw [he]

lemma originalRealPointsEquiv_entry (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ)
    (g : (ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).Points (RealPlaces.ArithmeticQuotient.realEmbedding μ)) (i j : Fin 3) :
    (originalRealPointsEquiv b hb δ hδ hδ0 μ g).val i j =
      RealQuadratic.ArithmeticQuotient.realQuadraticHom (RealPlaces.ArithmeticQuotient.realEmbedding μ (ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) (μ δ).im
        (imaginary_embedding_im_sq δ hδ μ)
        (ArithmeticQuotientEquationsData.decodeMatrix (RealPlaces.ArithmeticQuotient.realEmbedding μ (ArithmeticQuotientEquationsData.imaginarySquare δ hδ)) g.val.val i j) :=
  RealPoints.ArithmeticQuotient.realUnitaryPointsEquiv_entry _ _ _ _ _ g i j

lemma originalRealPointsEquiv_diagonal (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0) (μ : E →+* ℂ)
    (g : ArithmeticQuotientEquationsData.RationalSU b) :
    originalRealPointsEquiv b hb δ hδ hδ0 μ
      ((ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).map (RingHom.id _) (RealPlaces.ArithmeticQuotient.realEmbedding μ)
        (ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g)) = ArithmeticQuotientEquationsData.infinitePlaceMap b μ g := by
  apply Subtype.ext
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [originalRealPointsEquiv_entry]
  change RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ _ (ArithmeticQuotientEquationsData.decodeMatrix _
    ((ArithmeticQuotientSplitUnitary.originalUnitaryRationalEquiv b hb δ hδ hδ0 g).val.val.map (RealPlaces.ArithmeticQuotient.realEmbedding μ)) i j) = μ (g.val i j)
  rw [IntegralLattice.ArithmeticQuotient.originalUnitaryRationalEquiv_matrix, ← ArithmeticQuotientEquationsData.regularMatrix_map, ArithmeticQuotientEquationsData.decode_regularMatrix]
  change RealQuadratic.ArithmeticQuotient.realQuadraticHom _ _ _
    (ArithmeticQuotientEquationsData.quadraticMap _ (RealPlaces.ArithmeticQuotient.realEmbedding μ) ((ArithmeticQuotientEquationsData.quadraticEquiv δ hδ hδ0).symm (g.val i j))) = _
  rw [realQuadraticHom_scalarExtension δ hδ hδ0 μ, AlgEquiv.apply_symm_apply]

end

end OAI.Geometry.ComplexBall.Archimedean.ArithmeticQuotient
