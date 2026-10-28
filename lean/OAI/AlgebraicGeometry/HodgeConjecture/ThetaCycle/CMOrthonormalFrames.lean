import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMFormCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.DiagonalNormalization
import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoefficientSigns

/-! # CM Orthonormal Frames -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames.CM

noncomputable section

section

/-! ThetaCycle: explicit orthonormal bases for the actual local CM Hermitian
and multiplicity forms, with their distinguished and compact signs. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ)
  [NumberField K] [IsGalois ℚ K] [IsCMField K] (places : HeckeCycles.GeometricSource.CM.Places K)
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)

def sourceHermitianNormalizer (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
    (i : Fin places.count) : (Matrix (Fin 3) (Fin 3) ℂ)ˣ :=
  DiagonalNormalization.CM.complexDiagonalNormalizer (CMFormCoordinates.CM.sourceHermitianRealCoefficients K places β i)
    (CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero K places β hβ hβ0 i)

def sourceSkewNormalizer (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
    (i : Fin places.count) : (Matrix (Fin 2) (Fin 2) ℂ)ˣ :=
  DiagonalNormalization.CM.complexDiagonalNormalizer (CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a i)
    (CMFormCoordinates.CM.source_skew_coefficients_ne_zero K places δ hδ hδ0 a ha ha0 i)

theorem source_hermitian_normalized (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0)
    (i : Fin places.count) :
    (sourceHermitianNormalizer K places β hβ hβ0 i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
        (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
          (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i)) *
            (sourceHermitianNormalizer K places β hβ hβ0 i).val =
      Matrix.diagonal (fun j => if 0 < CMFormCoordinates.CM.sourceHermitianRealCoefficients K places β i j
        then (1 : ℂ) else -1) := by
  rw [CMFormCoordinates.CM.source_hermitian_local_matrix]
  simpa only [sourceHermitianNormalizer, mul_one] using! DiagonalNormalization.CM.complex_diagonal_normalizer_form
    (CMFormCoordinates.CM.sourceHermitianRealCoefficients K places β i)
    (CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero K places β hβ hβ0 i) 1

theorem source_skew_normalized (a : Fin 2 → K)
    (ha : ∀ j, IsCMField.complexConj K (a j) = a j) (ha0 : ∀ j, a j ≠ 0)
    (i : Fin places.count) :
    (sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
        (CMGlobalFrames.CM.cmSkewUnit K δ hδ hδ0 a ha ha0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
          (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i)) *
            (sourceSkewNormalizer K places δ hδ hδ0 a ha ha0 i).val =
      Matrix.diagonal (fun j => (if 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places δ a i j
        then (1 : ℂ) else -1) * Complex.I) := by
  rw [CMFormCoordinates.CM.source_skew_local_matrix]
  exact DiagonalNormalization.CM.complex_diagonal_normalizer_form _ _ Complex.I

theorem source_ball_hermitian_sign (B : HeckeCycles.GeometricSource.CM.BallDatum K) (i : Fin places.count) (j : Fin 3) :
    (if 0 < CMFormCoordinates.CM.sourceHermitianRealCoefficients K places B.b i j then (1 : ℂ) else -1) =
      if i = places.distinguished ∧ j = 2 then -1 else 1 := by
  by_cases hj : j = 2
  · subst j
    by_cases hi : i = places.distinguished
    · subst i
      have hneg := (HeckeCycles.ReferenceDatum.CM.source_signature K B places).2.2.1
      simp [CMFormCoordinates.CM.sourceHermitianRealCoefficients, not_lt.mpr hneg.le]
    · have hpos := (HeckeCycles.ReferenceDatum.CM.source_signature K B places).2.2.2 i hi
      simp [CMFormCoordinates.CM.sourceHermitianRealCoefficients, hi, hpos]
  · simp [CMFormCoordinates.CM.sourceHermitianRealCoefficients, hj]

theorem source_lagrangian_skew_coefficient_sign {B : HeckeCycles.GeometricSource.CM.BallDatum K}
    {d : Fin 2 → Fin places.count → Bool} (P : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ j, d j places.distinguished = true) (i : Fin places.count) (j : Fin 2) :
    if d j i then CMFormCoordinates.CM.sourceSkewRealCoefficients K places P.delta P.a i j < 0
      else 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places P.delta P.a i j := by
  by_cases hi : i = places.distinguished
  · subst i
    rw [hμ, ite_eq_left rfl]
    exact mul_neg_of_pos_of_neg (by norm_num) (P.a_sign j).2.2
  · have h := CoefficientSigns.CM.lagrangian_compact_coefficient_sign K d P j i hi
    cases hd : d j i <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at h ⊢
    · exact mul_pos (by norm_num) h
    · exact mul_neg_of_pos_of_neg (by norm_num) h

theorem source_lagrangian_skew_sign {B : HeckeCycles.GeometricSource.CM.BallDatum K}
    {d : Fin 2 → Fin places.count → Bool} (P : Lagrangians.CM.LagrangianPair K B places d)
    (hμ : ∀ j, d j places.distinguished = true) (i : Fin places.count) (j : Fin 2) :
    (if 0 < CMFormCoordinates.CM.sourceSkewRealCoefficients K places P.delta P.a i j then (1 : ℂ) else -1) * Complex.I =
      if !(d j i) then Complex.I else -Complex.I := by
  have h := source_lagrangian_skew_coefficient_sign K places P hμ i j
  cases hd : d j i <;> simp only [hd, Bool.false_eq_true, ite_false, ite_true] at h
  · simp [h]
  · simp [not_lt.mpr h.le]

end

/-! ThetaCycle: actual one-dimensional multiplicity frames, with the same CM
quadratic model and trace normalization as the total two-line construction. -/

open scoped Classical _root_.NumberField
open _root_.NumberField OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.GeometricSource.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReferenceDatum.CM

variable (K : IntermediateField ℚ ℂ) [NumberField K] [NumberField.IsCMField K]
  (δ : K) (hδ : IsCMField.complexConj K δ = -δ) (hδ0 : δ ≠ 0)
  (a : K) (ha : IsCMField.complexConj K a = a) (ha0 : a ≠ 0)

def singleLineRealCoefficient : Fin 1 → maximalRealSubfield K := fun _ => QuadraticModel.CM.cmRealElement K a ha

include ha0 in
theorem single_line_real_coefficient_ne_zero : ∀ j, singleLineRealCoefficient K a ha j ≠ 0 := by
  intro j h
  exact ha0 (congrArg (fun x : maximalRealSubfield K => (x : K)) h)

def singleLineSkewUnit :
    (Matrix (Fin 1) (Fin 1) (RepresentationTheory.Weil.AdelicSplitting.UnitaryBase.Construction.Quadratic (maximalRealSubfield K)
      (QuadraticModel.CM.cmQuadraticParameter K δ hδ)))ˣ :=
  DiagonalFrame.CM.diagonalSkewUnit _ (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (singleLineRealCoefficient K a ha) (single_line_real_coefficient_ne_zero K a ha ha0)

theorem single_line_skew_conjugate_transpose :
    (singleLineSkewUnit K δ hδ hδ0 a ha ha0).val.conjTranspose =
      -(singleLineSkewUnit K δ hδ hδ0 a ha ha0).val :=
  DiagonalFrame.CM.diagonal_skew_conjugateTranspose _ _

def singleLineGlobalFrames (β : K) (hβ : IsCMField.complexConj K β = β) (hβ0 : β ≠ 0) :
    RepresentationTheory.Weil.AdelicSplitting.Assembly.Construction.GlobalFrames (maximalRealSubfield K) (QuadraticModel.CM.cmQuadraticParameter K δ hδ) 3 1
      (CMGlobalFrames.CM.cmHermitianUnit K δ hδ β hβ hβ0) (singleLineSkewUnit K δ hδ hδ0 a ha ha0) :=
  GlobalFrames.CM.diagonalGlobalFrames _ _ (QuadraticModel.CM.cm_quadratic_parameter_ne_zero K δ hδ hδ0)
    (UnitaryFrame.CM.realHermitianCoefficients K β hβ) (CMGlobalFrames.CM.real_hermitian_coefficients_ne_zero K β hβ hβ0)
    (singleLineRealCoefficient K a ha) (single_line_real_coefficient_ne_zero K a ha ha0)

variable [IsGalois ℚ K] (places : HeckeCycles.GeometricSource.CM.Places K)

def singleLineSkewCoefficient (i : Fin places.count) : Fin 1 → ℝ :=
  fun _ => 2 * (HeckeCycles.ReferenceDatum.CM.embeddings K places i (δ * a)).im

include hδ hδ0 ha ha0 in
theorem single_line_skew_coefficient_ne_zero (i : Fin places.count) :
    ∀ j, singleLineSkewCoefficient K δ a places i j ≠ 0 := by
  intro _
  exact CMFormCoordinates.CM.source_skew_coefficients_ne_zero K places δ hδ hδ0 (fun _ => a)
    (fun _ => ha) (fun _ => ha0) i 0

def singleLineSkewNormalizer (i : Fin places.count) : (Matrix (Fin 1) (Fin 1) ℂ)ˣ :=
  DiagonalNormalization.CM.complexDiagonalNormalizer (singleLineSkewCoefficient K δ a places i)
    (single_line_skew_coefficient_ne_zero K δ hδ hδ0 a ha ha0 places i)

theorem single_line_skew_local_matrix (i : Fin places.count) :
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
      (singleLineSkewUnit K δ hδ hδ0 a ha ha0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
      (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i) =
        Matrix.diagonal (fun j => (singleLineSkewCoefficient K δ a places i j : ℂ) * Complex.I) := by
  ext j k
  have hj : j = 0 := Subsingleton.elim _ _
  have hk : k = 0 := Subsingleton.elim _ _
  subst j k
  exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (CMFormCoordinates.CM.source_skew_local_matrix K places δ hδ hδ0 (fun _ => a) (fun _ => ha) (fun _ => ha0) i)

theorem single_line_skew_normalized (i : Fin places.count) :
    (singleLineSkewNormalizer K δ hδ hδ0 a ha ha0 places i).val.conjTranspose *
      ((RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.localizedForm (maximalRealSubfield K)
        (singleLineSkewUnit K δ hδ hδ0 a ha ha0).val (.inl (RealPlaces.CM.sourceRealPlaces K places i))).map
        (CMArchimedeanCoordinates.CM.sourceConjugateComplexCoordinate K places δ hδ hδ0 i)) *
      (singleLineSkewNormalizer K δ hδ hδ0 a ha ha0 places i).val =
      Matrix.diagonal (fun j => (if 0 < singleLineSkewCoefficient K δ a places i j
        then (1 : ℂ) else -1) * Complex.I) := by
  rw [single_line_skew_local_matrix]
  exact DiagonalNormalization.CM.complex_diagonal_normalizer_form _ _ Complex.I

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CMOrthonormalFrames.CM
