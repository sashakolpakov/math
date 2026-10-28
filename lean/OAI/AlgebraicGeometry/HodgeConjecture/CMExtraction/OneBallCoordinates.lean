import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneDiagonalNormalizer
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodDomain

/-! # One Ball Coordinates -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallCoordinates.Multiplicity

noncomputable section

section

/-! The weighted native ball is carried to AdelicTheta's unit ball by the
positive radius determined by the same Hermitian coefficient. -/

open scoped Classical _root_.NumberField
open _root_.NumberField

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom)

include hP in
omit [IsGalois ℚ E] in
theorem nativeOneRadius_sq :
    OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished ^ 2 = -(P.μ P.b).re := by
  have hn : (P.embeddings P.distinguished P.b).re < 0 := hP.2.2.2.1
  change OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished ^ 2 = -(P.embeddings P.distinguished P.b).re
  rw [OneDiagonalNormalizer.Multiplicity.nativeOneRadius, Real.sq_sqrt (abs_nonneg _), abs_of_neg hn]

include hP hμ in
theorem nativeOne_active_coefficient :
    P.embeddings P.distinguished P.b = -(OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ) ^ 2 := by
  have h := ThetaCycle.CMFormCoordinates.CM.source_fixed_element_eq_real E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) P.b hP.2.1 P.distinguished
  rw [Intrinsic.IntrinsicOne.Multiplicity.nativePlaces_embeddings] at h
  rw [← h, ← Complex.ofReal_pow, nativeOneRadius_sq E P hP]
  simp
  rfl

def nativeOneBallPoint (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) : RepresentationTheory.Theta.Adelic.BallNatural.Ball :=
  ⟨fun j => z.val j / (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ), by
    have hr := OneDiagonalNormalizer.Multiplicity.nativeOneRadius_pos E P hP hμ P.distinguished
    have hz := (Set.ext_iff.mp (Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E P) z.val).mp z.property
    change Complex.normSq (z.val 0) + Complex.normSq (z.val 1) < -(P.μ P.b).re at hz
    change Complex.normSq (z.val 0 / (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)) +
      Complex.normSq (z.val 1 / (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)) < 1
    rw [Complex.normSq_div, Complex.normSq_div, ← add_div, Complex.normSq_ofReal]
    apply (div_lt_iff₀ (mul_pos hr hr)).mpr
    simpa only [one_mul, ← pow_two, nativeOneRadius_sq E P hP] using hz⟩

theorem nativeOneBallPoint_continuous : Continuous (nativeOneBallPoint E P hP hμ) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro j
  exact ((continuous_apply j).comp continuous_subtype_val).div_const _

end

/-! The rational AdelicTheta ball matrix is the original native unitary
matrix in the explicit radius-normalized coordinates. -/

open scoped Classical _root_.Matrix _root_.NumberField
open _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneDiagonalNormalizer.Quadratic OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.SpecialUnitary

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)

def nativeOneRationalSU : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b ≃* RepresentationTheory.Theta.Adelic.SpecialUnitary.SU (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP).val :=
  Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1

theorem nativeOneBasisV_val (i : Fin s) :
    ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).basisV i).val =
      Matrix.diagonal ![(1 : ℂ), 1, (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P i : ℂ)⁻¹] := by
  change (ThetaCycle.DiagonalNormalization.CM.complexDiagonalNormalizer
    (ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ) P.b i)
    (ThetaCycle.CMFormCoordinates.CM.source_hermitian_coefficients_ne_zero E (Intrinsic.Representatives.Multiplicity.nativePlaces E P hP hμ)
      P.b hP.2.1 hP.2.2.1 i)).val = _
  apply congrArg Matrix.diagonal
  funext j
  fin_cases j <;>
    simp [ThetaCycle.DiagonalNormalization.CM.diagonalNormalizationScale,
      ThetaCycle.CMFormCoordinates.CM.sourceHermitianRealCoefficients, OneDiagonalNormalizer.Multiplicity.nativeOneRadius, Intrinsic.IntrinsicOne.Multiplicity.nativePlaces_embeddings]

theorem nativeOneRational_arch_matrix (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (i : Fin s) :
    ((RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
      (nativeOneRationalSU E P hP γ) ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).enumerate i)).val.val.map
      ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).complex i)) =
      γ.val.val.map (P.embeddings i) := by
  funext j k
  change (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).complex i
    (RepresentationTheory.Weil.AdelicSplitting.Integral.Construction.rationalQuadraticLocal (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneParameter E P hP)
      (.inl ((Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv).enumerate i))
      ((nativeOneRationalSU E P hP γ).val.val j k)) = _
  rw [Intrinsic.OneCoordinates.Multiplicity.nativeOneBall_embedding]
  change P.embeddings i (ThetaCycle.QuadraticModel.CM.cmQuadraticEquiv E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP)
    ((Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation E P.imaginaryScalar (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaImaginary E P hP)
      (Intrinsic.OneTheta.Multiplicity.nativeOneDeltaNonzero E P hP) P.b hP.2.1 hP.2.2.1 γ).val.val j k)) = _
  rw [Multiplicity.OneUnitary.Quadratic.cmRationalUnitaryPresentation_matrix, Matrix.map_apply, AlgEquiv.apply_symm_apply]
  rfl

theorem nativeOne_standardMatrix (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) (i : Fin s) :
    RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv)
      (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
        (nativeOneRationalSU E P hP γ)) i =
      Matrix.diagonal ![(1 : ℂ), 1, (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P i : ℂ)] *
        γ.val.val.map (P.embeddings i) *
          Matrix.diagonal ![(1 : ℂ), 1, (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P i : ℂ)⁻¹] := by
  unfold RepresentationTheory.Theta.Adelic.BallGeometryData.standardMatrix
  exact congrArg₂ (fun A B : Matrix (Fin 3) (Fin 3) ℂ => A * B)
    (congrArg₂ (fun A B : Matrix (Fin 3) (Fin 3) ℂ => A * B)
      (OneDiagonalNormalizer.Multiplicity.nativeOneBasisV_inv E P hP hμ hs v hv i)
      (nativeOneRational_arch_matrix E P hP hμ hs v hv γ i))
    (nativeOneBasisV_val E P hP hμ hs v hv i)

theorem nativeOne_comparison_ball_matrix
    (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
      (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
    (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B) (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b) :
    (RepresentationTheory.Theta.Adelic.BallNatural.asSL (B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (nativeOneRationalSU E P hP γ)))).val =
      Matrix.diagonal ![(1 : ℂ), 1, (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)] *
        γ.val.val.map P.μ *
          Matrix.diagonal ![(1 : ℂ), 1, (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)⁻¹] :=
  (hGeometry.2.1 _).trans (nativeOne_standardMatrix E P hP hμ hs v hv γ P.distinguished)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallCoordinates.Multiplicity
