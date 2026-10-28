import OAI.RepresentationTheory.Theta.Geometric.Universal.HodgeComparison
import OAI.RepresentationTheory.Theta.Geometric.Relative.LevelIso
import OAI.RepresentationTheory.Theta.Geometric.DistinctFiberPELComparison
import OAI.RepresentationTheory.Theta.Geometric.Universal.ModuliFaithfulness

/-! # Ball Injectivity -/

namespace OAI.RepresentationTheory.Theta.Geometric.Universal.BallInjectivity

noncomputable section

section

/-! The actual local distinguished period kernel determines the
original universal-family moduli point, with every PEL structure retained. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

theorem complexUniversal_point_eq_of_kernel_eq (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) (e₀ : Geometry.ComplexBall.PrescribedSignsB.Vec ≃ₗ[ℂ] Geometry.ComplexBall.PrescribedSignsB.Vec)
    (z w : (HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).compatible.neighborhood)
    (heq : ((HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).embeddingMatrix s hs rfl hdegree
      (D.reference.embeddings D.reference.distinguished) e₀ z).ker =
      ((HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x).embeddingMatrix s hs rfl hdegree
        (D.reference.embeddings D.reference.distinguished) e₀ w).ker) :
    Intrinsic.FamilyFrames.familyChartParameter (FamilyPeriodCharts.complexUniversalFamilyCharts D f x) z ≫ f =
      Intrinsic.FamilyFrames.familyChartParameter (FamilyPeriodCharts.complexUniversalFamilyCharts D f x) w ≫ f := by
  let A := PELConditions.complexUniversalPolarized D hg f
  let ρ := PELConditions.complexUniversalAction D hg f
  let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
  let H := HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x
  have hH := HodgeComparison.complexUniversal_isHodgeMap_of_kernel_eq D hg f x hs hdegree e₀ z w heq
  let e := H.compatible.levelIso A ρ z w hH
  let p := DistinctFiberPELComparison.pelFiberIsoOfPolarized (Complex.PELClassification.complexUniversalFamily D f) (PELConditions.complexUniversal_isPELFamily D hg f).1
    (Intrinsic.FamilyFrames.familyChartParameter C z).left (Intrinsic.FamilyFrames.familyChartParameter C w).left e
    (H.compatible.levelIso_action A ρ z w hH)
  exact ModuliFaithfulness.complexUniversal_point_eq_of_iso D hg f (Intrinsic.FamilyFrames.familyChartParameter C z) (Intrinsic.FamilyFrames.familyChartParameter C w) p

end

/-! The constructed local ball periods of an actual smooth integral
moduli subspace are injective, by original full PEL classification. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped Classical

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    {S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral S.left] [Smooth S.hom]
    (f : S ⟶ D.complexSpace) [Mono f] (x : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)

include hg in
theorem exists_complexUniversal_injective_ball_periods (hs : 0 < s)
    (hdegree : Module.finrank ℚ E = 2 * s) :
    let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
    ∃ (O : Set (Intrinsic.FamilyFrames.FamilyChartBase C)) (period : Intrinsic.FamilyFrames.FamilyChartBase C → Geometry.ComplexBall.PrescribedSignsB.BallChart),
      IsOpen O ∧ Intrinsic.FamilyFrames.familyChartCenter C ∈ O ∧
      DifferentiableOn ℂ period O ∧ Set.MapsTo period O D.reference.domain ∧ Set.InjOn period O := by
  let C := FamilyPeriodCharts.complexUniversalFamilyCharts D f x
  let H := HolomorphicTransport.complexUniversalHolomorphicTransport D hg f x
  obtain ⟨e₀, O, period, hO, hxO, hsub, _, hhol, hp⟩ :=
    BallPeriods.exists_complexUniversal_ball_periods D hg f x hs hdegree
  refine ⟨O, period, hO, hxO, hhol, fun z hz => (hp z hz).1, ?_⟩
  intro z hz w hw heq
  have hker := (hp z hz).2.trans
    ((congrArg (fun v : Geometry.ComplexBall.PrescribedSignsB.BallChart => Submodule.span ℂ {Geometry.ComplexBall.PrescribedSignsB.lineVector v}) heq).trans (hp w hw).2.symm)
  have hpoint := complexUniversal_point_eq_of_kernel_eq D hg f x hs hdegree e₀
    ⟨z, hsub hz⟩ ⟨w, hsub hw⟩ hker
  exact Family.ChartOpenImage.familyChartParameter_injective C
    (H.compatible.subset_chart (hsub hz)) (H.compatible.subset_chart (hsub hw))
    ((cancel_mono f).mp hpoint)

end

end OAI.RepresentationTheory.Theta.Geometric.Universal.BallInjectivity
