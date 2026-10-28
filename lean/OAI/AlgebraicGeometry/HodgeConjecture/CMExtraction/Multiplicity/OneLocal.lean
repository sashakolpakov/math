import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneFrames
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames

/-! # One Local -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneLocal.Quadratic

noncomputable section

/-! The actual local skew-Hermitian form of one multiplicity line and its
orthonormal basis in the same CM completion coordinates. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsGalois ℚ E] [IsCMField E]
  (places : HeckeCycles.GeometricSource.CM.Places E)
  (δ : E) (hδ : IsCMField.complexConj E δ = -δ) (hδ0 : δ ≠ 0)
  (a : E) (ha : IsCMField.complexConj E a = a) (ha0 : a ≠ 0)

def singleSkewRealCoefficient (i : Fin places.count) : ℝ :=
  2 * (HeckeCycles.ReferenceDatum.CM.embeddings E places i (δ * a)).im

include hδ hδ0 ha ha0 in
theorem singleSkewRealCoefficient_ne_zero (i : Fin places.count) :
    singleSkewRealCoefficient E places δ a i ≠ 0 := by
  exact ThetaCycle.CMFormCoordinates.CM.source_skew_coefficients_ne_zero E places δ hδ hδ0 (fun _ => a)
    (fun _ => ha) (fun _ => ha0) i 0

theorem singleSkewUnit_local (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E)
      (OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 a ha ha0).val (.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places i))).map
        (ThetaCycle.CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate E places δ hδ hδ0 i) =
      Matrix.diagonal (fun _ : Fin 1 => (singleSkewRealCoefficient E places δ a i : ℂ) * Complex.I) := by
  apply Matrix.ext
  intro j k
  fin_cases j
  fin_cases k
  have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (ThetaCycle.CMFormCoordinates.CM.source_skew_local_matrix E places δ hδ hδ0 (fun _ => a) (fun _ => ha) (fun _ => ha0) i)
  exact h

def singleSkewNormalizer (i : Fin places.count) : (Matrix (Fin 1) (Fin 1) ℂ)ˣ :=
  ThetaCycle.DiagonalNormalization.CM.complexDiagonalNormalizer (fun _ => singleSkewRealCoefficient E places δ a i)
    (fun _ => singleSkewRealCoefficient_ne_zero E places δ hδ hδ0 a ha ha0 i)

theorem singleSkewUnit_normalized (i : Fin places.count) :
    (singleSkewNormalizer E places δ hδ hδ0 a ha ha0 i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield E)
        (OneFrames.Quadratic.singleSkewUnit E δ hδ hδ0 a ha ha0).val (.inl (ThetaCycle.RealPlaces.CM.sourceRealPlaces E places i))).map
          (ThetaCycle.CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate E places δ hδ hδ0 i)) *
        (singleSkewNormalizer E places δ hδ hδ0 a ha ha0 i).val =
      Matrix.diagonal (fun _ : Fin 1 =>
        (if 0 < singleSkewRealCoefficient E places δ a i then (1 : ℂ) else -1) * Complex.I) := by
  rw [singleSkewUnit_local]
  exact ThetaCycle.DiagonalNormalization.CM.complex_diagonal_normalizer_form _ _ Complex.I

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.OneLocal.Quadratic
