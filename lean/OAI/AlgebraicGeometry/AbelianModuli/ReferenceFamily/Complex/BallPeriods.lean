import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Smooth.BallPeriods
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Complex.FiberBallPoint

/-! # Ball Periods -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily

noncomputable section

/-! Actual PEL families on smooth complex bases construct local native
period maps into the prescribed ball, using their original Lie ranks. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type} [Field K]

def Complex.BallPeriods.restrictComplexBase (κ : K →+* ℂ) (S : Over Foundations.Scheme.ProjectiveSpace.complexBase) : Over (Spec (.of K)) :=
  (Over.map (Spec.map (CommRingCat.ofHom κ))).obj S

theorem Complex.BallPeriods.restrictComplexBase_point (κ : K →+* ℂ) {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
    y.left ≫ (Complex.BallPeriods.restrictComplexBase κ S).hom = Spec.map (CommRingCat.ofHom κ) := by
  change y.left ≫ (S.hom ≫ Spec.map (CommRingCat.ofHom κ)) = _
  rw [← Category.assoc, y.w]
  exact Category.id_comp _

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {s N : ℕ} {P : Datum.RankThreePELDatum E s} {iota : E →+* K}
    (κ : K →+* ℂ) (hκ : κ.comp iota = P.μ)
    {S : Over Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (A : PEL.Objects.PELObject P iota N (Complex.BallPeriods.restrictComplexBase κ S))

include hκ in
theorem PEL.Objects.PELObject.exists_complex_family_ball_periods
    (hs : 0 < s) (hdegree : Module.finrank ℚ E = 2 * s) (hP : P.IsAdmissible)
    (x : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) (hN : 0 < N) :
    ∃ (C : PELModuli.CMPoints.IntrinsicFamilyCharts.NativeFamilyCharts A.polarized.abelian x) (F : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.NativeFamilyPeriodFrame C)
      (H : Intrinsic.HolomorphicTransport.NativeFamilyHolomorphicTransport A.polarized A.action F)
      (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec) (O : Set (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C)) (period : RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C ∈ O ∧ O ⊆ H.compatible.neighborhood ∧
      (∀ v w, Complex.HermitianMatrixForm.complexHermitianMatrixForm
        ((RepresentationTheory.Theta.Geometric.Family.HermitianTransport.familyHermitianMatrix A.polarized A.action A.rosati
          (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartParameter C (RepresentationTheory.Theta.Geometric.Intrinsic.FamilyFrames.familyChartCenter C)) s hs rfl hdegree P.normalizedImaginaryScalar).map
          (P.embeddings P.distinguished)) (e₀ v) (e₀ w) =
        Complex.HermitianMatrixForm.complexHermitianMatrixForm (Matrix.diagonal ![1, 1, P.μ P.b]) v w) ∧
      DifferentiableOn ℂ period O ∧ ∀ z ∈ O,
        period z ∈ P.domain ∧
        (H.embeddingMatrix s hs rfl hdegree (P.embeddings P.distinguished) e₀ z).ker =
          Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector (period z)} := by
  obtain ⟨hξ, hc, hi⟩ := Datum.RankThreePELDatum.normalizedImaginaryScalar_spec hP
  have hr (y : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S) :
      LieRanks.HasLieRank (A.polarized.abelian.pullback y.left) (A.action.pullback y.left)
        (P.μ.comp (algebraMap (NumberField.RingOfIntegers E) E)) 2 :=
    A.complexFiber_distinguished_rank κ hκ y.left (Complex.BallPeriods.restrictComplexBase_point κ y) hP
  obtain ⟨C, F, H, e₀, O, period, hO, hx, hsub, he, hhol, hp⟩ :=
    ReferenceFamily.Smooth.BallPeriods.exists_smooth_family_ball_periods A.polarized A.action x hN A.rosati s hs rfl hdegree
      P.normalizedImaginaryScalar hξ hc (P.embeddings P.distinguished) hi P.b hP.2.1 hP.2.2.2.1 hr
  refine ⟨C, F, H, e₀, O, period, hO, hx, hsub, he, hhol, ?_⟩
  intro z hz
  exact ⟨(Datum.RankThreePELDatum.mem_domain_iff_diagonal (period z)).mpr (hp z hz).2, (hp z hz).1⟩

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily
