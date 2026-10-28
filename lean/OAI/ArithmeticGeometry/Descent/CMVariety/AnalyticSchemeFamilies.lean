import OAI.ArithmeticGeometry.Descent.CMVariety.RelativeTensorPoints
import OAI.AlgebraicGeometry.ComplexPoints.Analytic.AffineOverlap

/-! # Analytic Scheme Families -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts

noncomputable section

/-!
Actual scheme morphisms preserve analytically varying affine point families
in the constructed coordinates. The algebra map on a principal neighborhood
is obtained from the scheme morphism and the target affine open immersion.
It is not supplied as an additional local comparison hypothesis.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical ContDiff _root_.Topology

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase}

/-- Lift any of the constructed analytic model charts through the actual
affine open immersion, without a restriction on its coordinate index type. -/
def nativeAffineChart (B : CommAlgCat ℂ)
    (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y) [IsOpenImmersion j.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) F) :
    OpenPartialHomeomorph (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) F :=
  e.lift_openEmbedding (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j)

omit [NormedSpace ℂ F] in
/-- The actual chart-overlap domain is open, as follows from the native
point topology and the regular-function evaluation topology. -/
theorem isOpen_schemeImage_affineChart_domain (A B : CommAlgCat ℂ)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    [IsOpenImmersion j.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) F)
    (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (U : Set E) (hU : IsOpen U)
    (hf : ∀ a : A, ContDiffOn ℂ ω (fun z => f z a) U) :
    IsOpen (U ∩ {z | AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (f z) ∈
      (nativeAffineChart B j e).source}) := by
  have hc := RegularRelativeCharts.Abelian.RelativeCharts.continuousOn_affinePoints_of_evaluations f U (fun a => (hf a).continuousOn)
  exact ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap A i).continuousOn.comp hc
    (mapsTo_univ _ _)).isOpen_inter_preimage hU (nativeAffineChart B j e).open_source

/-- Any actual morphism from an affine scheme takes an analytic family
of algebra characters to an analytic coordinate family. Local algebra
factorizations and their neighborhoods are constructed from the morphism. -/
theorem contDiffOn_schemeImage_in_affineChart (A B : CommAlgCat ℂ)
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ Y) (j : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ B ⟶ Y)
    [IsOpenImmersion j.left]
    (e : OpenPartialHomeomorph (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B) F)
    (he : RegularRelativeCharts.Abelian.RelativeCharts.HasAnalyticCoordinates e)
    (f : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A) (U : Set E) (hU : IsOpen U)
    (hf : ∀ a : A, ContDiffOn ℂ ω (fun z => f z a) U) :
    ContDiffOn ℂ ω
      (fun z => nativeAffineChart B j e (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (f z)))
      (U ∩ {z | AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (f z) ∈
        (nativeAffineChart B j e).source}) := by
  intro z hz
  obtain ⟨y, hy, hxy⟩ := hz.2
  obtain ⟨a, ha, h, _, hpoint⟩ :=
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.exists_affineLocalizationTransition A B i j (f z) ⟨y, hxy⟩
  let V := U ∩ {w | f w a ≠ 0}
  have hV : IsOpen V := (hf a).continuousOn.isOpen_inter_preimage hU isOpen_ne
  have hzV : z ∈ V := ⟨hz.1, ha⟩
  obtain ⟨fg, hfg, hreg⟩ := RelativeTensorPoints.Abelian.RelativeCharts.exists_analytic_localizedFamily a f U hf
    (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint (f z) a ha)
  let q : E → AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints B := fun w => (fg w).comp h
  have hlocal (w : E) (hw : w ∈ V) :
      fg w = AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint (f w) a hw.2 := by
    apply (AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints.isOpenEmbedding_localizationRestriction a).injective
    rw [hfg w hw]
    exact (AlgebraicGeometry.Foundations.Scheme.LocalizationComplexPoints.Algebraic.localizePoint_comp (f w) a hw.2).symm
  have hsame (w : E) (hw : w ∈ V) :
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j (q w) =
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap A i (f w) := by
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap B j ((fg w).comp h) = _
    rw [hlocal w hw]
    exact hpoint ⟨f w, hw.2⟩
  have hqz : q z = y :=
    (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap B j).injective ((hsame z hzV).trans hxy.symm)
  have hq : ContinuousOn q V :=
    RegularRelativeCharts.Abelian.RelativeCharts.continuousOn_affinePoints_of_evaluations q V (fun b => (hreg (h b)).continuousOn)
  let W := V ∩ q ⁻¹' e.source
  have hW : IsOpen W := hq.isOpen_inter_preimage hV e.open_source
  have hzW : z ∈ W := ⟨hzV, (congrArg (fun b => b ∈ e.source) hqz).mpr hy⟩
  have hc : ContDiffAt ℂ ω (fun w => e (q w)) z :=
    (he E q V (fun b => hreg (h b))).contDiffAt (hW.mem_nhds hzW)
  apply ContDiffAt.contDiffWithinAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [hW.mem_nhds hzW] with w hw
  rw [← hsame w hw.1]
  exact OpenPartialHomeomorph.lift_openEmbedding_apply _ _

end

end OAI.ArithmeticGeometry.Descent.CMVariety.AnalyticSchemeFamilies.Abelian.RelativeCharts
