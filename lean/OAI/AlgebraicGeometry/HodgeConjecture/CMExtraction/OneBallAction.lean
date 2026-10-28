import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.RadiusChartConjugation
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarConjugateDerivative
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ArchFrame
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.PeriodAction

/-! # One Ball Action -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallAction.Multiplicity

noncomputable section

/-! The same AdelicTheta comparison intertwines the original rational ball
action and its actual cotangent differential. -/

open scoped Classical _root_.Matrix _root_.NumberField _root_.Topology
open _root_.Matrix _root_.NumberField

open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.ArchFrame OAI.RepresentationTheory.Theta.Adelic.BallGeometryData OAI.RepresentationTheory.Theta.Adelic.DataTheta
open OAI.RepresentationTheory.Theta.Adelic.RationalSU OAI.RepresentationTheory.Theta.Adelic.DeterminantCoordinates

attribute [local instance] Intrinsic.PeriodAction.Multiplicity.nativeDomainAction

variable (E : IntermediateField ℚ ℂ) [NumberField E] [IsCMField E] [IsGalois ℚ E]
  {s : ℕ} (P : AbelianModuli.ReferenceFamily.Datum.RankThreePELDatum E s) (hP : P.IsAdmissible)
  (hμ : P.μ = E.val.toRingHom) (hs : 2 ≤ s) (v : Multiplicity.Odd.Sign E) (hv : v.val 1 = true)
  (B : RepresentationTheory.Theta.Adelic.DataTheta.ComparisonData (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
    (Intrinsic.OneTheta.Multiplicity.nativeOneSkew E P hP v) (Intrinsic.OneTheta.Multiplicity.nativeOneBall E P hP hμ hs v hv))
  (hGeometry : RepresentationTheory.Theta.Adelic.DataTheta.GeometryIdentification B)

theorem nativeOneBallPoint_scale (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ) • (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z).val = z.val := by
  have hr : (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (OneDiagonalNormalizer.Multiplicity.nativeOneRadius_pos E P hP hμ P.distinguished).ne'
  funext i
  change (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ) *
    (z.val i / (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)) = z.val i
  exact mul_div_cancel₀ _ hr

include hGeometry in
theorem nativeOneBallPoint_action (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E) (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP)
      (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)) • OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z =
      OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ (γ • z) := by
  have hr : (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (OneDiagonalNormalizer.Multiplicity.nativeOneRadius_pos E P hP hμ P.distinguished).ne'
  apply Subtype.ext
  change RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage (RepresentationTheory.Theta.Adelic.BallNatural.asSL (B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E)
    (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ))))
    (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z).val = _
  rw [RadiusChartConjugation.TestTransport.radius_chart_conjugation (Intrinsic.ArchFrame.archUnitaryBlock E P P.distinguished γ) _
    (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ) hr
    (OneBallCoordinates.Multiplicity.nativeOne_comparison_ball_matrix E P hP hμ hs v hv B hGeometry γ),
    nativeOneBallPoint_scale, Intrinsic.ArchFrame.native_chartImage_eq_periodMap E P γ z.val z.property]
  funext i
  change (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)⁻¹ * (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ z.val) i =
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ z.val) i / (OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished : ℂ)
  rw [div_eq_mul_inv, mul_comm]

include hGeometry in
theorem nativeOneBallPoint_derivative (γ : Geometry.ComplexBall.ArithmeticQuotientEquationsData.RationalSU P.b)
    (z : {z : Geometry.ComplexBall.PrescribedSignsB.BallChart // z ∈ P.domain}) :
    fderiv ℂ (RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage (RepresentationTheory.Theta.Adelic.BallNatural.asSL (B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)))))
      (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z).val = fderiv ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ) z.val := by
  let r : ℂ := OneDiagonalNormalizer.Multiplicity.nativeOneRadius E P P.distinguished
  have hr : r ≠ 0 := Complex.ofReal_ne_zero.mpr (OneDiagonalNormalizer.Multiplicity.nativeOneRadius_pos E P hP hμ P.distinguished).ne'
  let F := RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage (Intrinsic.ArchFrame.archUnitaryBlock E P P.distinguished γ)
  have hO : IsOpen P.domain := by
    rw [Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E P]
    exact (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b)).isOpen
  have heq : F =ᶠ[𝓝 z.val] RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ :=
    Filter.eventually_of_mem (hO.mem_nhds z.property)
      (fun x hx => Intrinsic.ArchFrame.native_chartImage_eq_periodMap E P γ x hx)
  have hz : z.val ∈ Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) := by
    change z.val ∈ (Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b) : Set Geometry.ComplexBall.PrescribedSignsB.BallChart)
    rw [← Intrinsic.PeriodDomain.Multiplicity.native_domain_eq_ball E P]
    exact z.property
  have hd : DifferentiableAt ℂ (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm P.b P.μ γ) z.val :=
    (RepresentationTheory.Theta.Geometric.Period.Ne.rationalPeriodPerm_differentiableOn P.b P.μ γ z.val hz).differentiableAt
      ((Geometry.ComplexBall.ArithmeticQuotientBoostBall.ballOpen (P.μ P.b)).isOpen.mem_nhds hz)
  have hF : DifferentiableAt ℂ F z.val := heq.differentiableAt_iff.mpr hd
  have hscale : r • (OneBallCoordinates.Multiplicity.nativeOneBallPoint E P hP hμ z).val = z.val :=
    nativeOneBallPoint_scale E P hP hμ z
  have hchart : RepresentationTheory.Theta.Adelic.DeterminantCoordinates.chartImage (RepresentationTheory.Theta.Adelic.BallNatural.asSL (B.ball (RepresentationTheory.Theta.Adelic.RationalSU.rationalArchimedeanSU (maximalRealSubfield E)
      (Intrinsic.OneTheta.Multiplicity.nativeOneHermitian E P hP) (OneBallCoordinates.Multiplicity.nativeOneRationalSU E P hP γ)))) =
      (fun x => r⁻¹ • F (r • x)) := by
    funext x
    exact RadiusChartConjugation.TestTransport.radius_chart_conjugation (Intrinsic.ArchFrame.archUnitaryBlock E P P.distinguished γ) _ r hr
      (OneBallCoordinates.Multiplicity.nativeOne_comparison_ball_matrix E P hP hμ hs v hv B hGeometry γ) x
  rw [hchart, ScalarConjugateDerivative.TestTransport.fderiv_scalar_conjugate F r hr _ (hscale.symm ▸ hF), hscale]
  exact heq.fderiv_eq

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OneBallAction.Multiplicity
