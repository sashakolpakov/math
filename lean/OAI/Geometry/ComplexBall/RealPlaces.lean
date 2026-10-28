import OAI.Geometry.ComplexBall.Connected
import OAI.Geometry.ComplexBall.RealPoints
import OAI.NumberTheory.ArithmeticGroups.Lattices.Realizations

/-! # Real Places -/

namespace OAI.Geometry.ComplexBall.RealPlaces.ArithmeticQuotient

noncomputable section

/-! The real embeddings and compact omitted factors in the arithmetic
presentation of the original CM unitary group. -/

open scoped Classical
open _root_.NumberField

variable {E : Type} [Field E] [NumberField E]

def realEmbedding (μ : E →+* ℂ) : ArithmeticQuotientEquationsData.RealField E →+* ℝ :=
  (IsTotallyReal.complexEmbedding_isReal (μ.comp (algebraMap (ArithmeticQuotientEquationsData.RealField E) E))).embedding

lemma realEmbedding_apply (μ : E →+* ℂ) (x : ArithmeticQuotientEquationsData.RealField E) :
    realEmbedding μ x = (μ (x : E)).re := rfl

lemma realEmbedding_coe (μ : E →+* ℂ) (x : ArithmeticQuotientEquationsData.RealField E) :
    (realEmbedding μ x : ℂ) = μ (x : E) :=
  ComplexEmbedding.IsReal.coe_embedding_apply _ x

lemma realEmbedding_conjugate (μ : E →+* ℂ) :
    realEmbedding ((starRingEnd ℂ).comp μ) = realEmbedding μ := by
  ext x
  change (star (μ (x : E))).re = (μ (x : E)).re
  rfl

lemma realEmbedding_lift (v : ArithmeticQuotientEquationsData.RealField E →+* ℝ) :
    realEmbedding (ComplexEmbedding.lift E (Complex.ofRealHom.comp v)) = v := by
  ext x
  change (ComplexEmbedding.lift E (Complex.ofRealHom.comp v)
    (algebraMap (ArithmeticQuotientEquationsData.RealField E) E x)).re = v x
  rw [ComplexEmbedding.lift_algebraMap_apply]
  rfl

def realPlace (μ : E →+* ℂ) : InfinitePlace (ArithmeticQuotientEquationsData.RealField E) :=
  InfinitePlace.mk (Complex.ofRealHom.comp (realEmbedding μ))

omit [NumberField E] in
lemma realPlace_embedding (v : InfinitePlace (ArithmeticQuotientEquationsData.RealField E)) (hv : v.IsReal) :
    InfinitePlace.mk (Complex.ofRealHom.comp (v.embedding_of_isReal hv)) = v := by
  have he : Complex.ofRealHom.comp (v.embedding_of_isReal hv) = v.embedding := by
    ext x
    exact InfinitePlace.embedding_of_isReal_apply hv x
  rw [he, InfinitePlace.mk_embedding]

variable [IsCMField E]

lemma imaginary_square_negative_real (δ : E) (hδ : IsCMField.complexConj E δ = -δ)
    (hδ0 : δ ≠ 0) (v : ArithmeticQuotientEquationsData.RealField E →+* ℝ) : v (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) < 0 := by
  have h := ArithmeticQuotientEquationsData.imaginary_square_negative δ hδ hδ0
    (ComplexEmbedding.lift E (Complex.ofRealHom.comp v))
  change realEmbedding (ComplexEmbedding.lift E (Complex.ofRealHom.comp v))
    (ArithmeticQuotientEquationsData.imaginarySquare δ hδ) < 0 at h
  rwa [realEmbedding_lift] at h

lemma signature_positive_at_other_real_embedding (b : E)
    (hb : IsCMField.complexConj E b = b) (μ : E →+* ℂ)
    (hpos : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re)
    (v : ArithmeticQuotientEquationsData.RealField E →+* ℝ) (hv : v ≠ realEmbedding μ) : 0 < v (ArithmeticQuotientSplitUnitary.realCoefficient b hb) := by
  let ν := ComplexEmbedding.lift E (Complex.ofRealHom.comp v)
  have he : realEmbedding ν = v := realEmbedding_lift v
  have hν : ν ≠ μ := fun h => hv (he.symm.trans (congrArg realEmbedding h))
  have hνc : ν ≠ (starRingEnd ℂ).comp μ := by
    intro h
    exact hv (he.symm.trans ((congrArg realEmbedding h).trans (realEmbedding_conjugate μ)))
  have h := hpos ν hν hνc
  change 0 < realEmbedding ν (ArithmeticQuotientSplitUnitary.realCoefficient b hb) at h
  rwa [he] at h

lemma originalUnitaryPoints_compact (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (v : ArithmeticQuotientEquationsData.RealField E →+* ℝ) (hvb : 0 < v (ArithmeticQuotientSplitUnitary.realCoefficient b hb)) :
    CompactSpace ((ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).Points v) :=
  RealPoints.ArithmeticQuotient.realUnitaryPoints_compact_of_positive (v (ArithmeticQuotientEquationsData.imaginarySquare δ hδ))
    (v (ArithmeticQuotientSplitUnitary.realCoefficient b hb)) (imaginary_square_negative_real δ hδ hδ0 v) hvb

lemma originalUnitary_omittedPlace_compact (b : E) (hb : IsCMField.complexConj E b = b)
    (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
    (μ : E →+* ℂ)
    (hpos : ∀ ν : E →+* ℂ, ν ≠ μ → ν ≠ (starRingEnd ℂ).comp μ → 0 < (ν b).re)
    (v : InfinitePlace (ArithmeticQuotientEquationsData.RealField E)) (hv : v ≠ realPlace μ) :
    CompactSpace ((ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).AtPlace v) := by
  have hreal := IsTotallyReal.isReal v
  have he : v.embedding_of_isReal hreal ≠ realEmbedding μ := by
    intro h
    apply hv
    rw [← realPlace_embedding v hreal, h]
    rfl
  have hp := signature_positive_at_other_real_embedding b hb μ hpos _ he
  let : CompactSpace ((ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).Points
      (v.embedding_of_isReal hreal)) := originalUnitaryPoints_compact b hb δ hδ hδ0 _ hp
  exact ((ArithmeticQuotientSplitUnitary.originalUnitaryAlgebraicGroup b hb δ hδ).realPlaceEquiv v hreal).symm.toHomeomorph.compactSpace

end

end OAI.Geometry.ComplexBall.RealPlaces.ArithmeticQuotient
