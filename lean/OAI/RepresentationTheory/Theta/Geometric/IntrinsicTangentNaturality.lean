import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts
import OAI.RepresentationTheory.Theta.Geometric.JetOpenNaturality

/-! # Intrinsic Tangent Naturality -/

namespace OAI

noncomputable section

namespace RepresentationTheory.Theta.Geometric.IntrinsicTangentNaturality.NativeTangentChart

/-! The actual manifold derivative equals the map on native dual-number
tangent points for every morphism of smooth integral complex schemes. -/

open scoped _root_.Manifold ContDiff
open _root_.CategoryTheory _root_.AlgebraicGeometry ChartedSpace

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X} (C : Intrinsic.TangentCharts.NativeTangentChart X p)

instance : Nonempty C.U := by
  have hp : p ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenPointMap X C.U C.affine) :=
    ⟨C.point, C.point_eq⟩
  rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.range_affineOpenPointMap] at hp
  exact ⟨⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.underlying p, hp⟩⟩

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.tangentEquiv_jet (v : Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) :
    (C.tangentEquiv v).val =
      ChartJets.regularChartSpecJet C.chart C.regular C.point C.source v ≫
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine := rfl

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.chart_apply :
    chartAt (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ) p p =
      C.chart C.point := by
  rw [C.chart_eq]
  exact (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme C.algebra
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine) C.chart) C.point_eq.symm).trans
      (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme_apply _ _ _ _)

variable {Y : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral Y.left] [Smooth Y.hom]
  (φ : X ⟶ Y) (D : Intrinsic.TangentCharts.NativeTangentChart Y (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p))

local notation "ModelX" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)
local notation "ModelY" => (Fin (OAI.AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension Y.hom) → ℂ)

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.mfderiv_charts :
    mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) p =
      fderiv ℂ (fun z => AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.affineChartOnScheme D.algebra
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y D.U D.affine) D.chart
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra
          (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine ≫ φ) (C.chart.symm z)))
        (C.chart C.point) := by
  have hd := (AlgebraicGeometry.ComplexPoints.Analytic.IntrinsicSmoothSchemeMaps.contMDiff_nativeScheme_map φ ∞).mdifferentiableAt (x := p) (by simp)
  simp only [mfderiv, hd, ↓reduceIte, writtenInExtChartAt, mfld_simps,
    fderivWithin_univ]
  rw [C.chart_apply, C.chart_eq, D.chart_eq]
  rfl

theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.tangentEquiv_naturality (v : ModelX) :
    (D.tangentEquiv
      (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) p v)).val =
        (C.tangentEquiv v).val ≫ φ := by
  have hxy : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap D.algebra
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y D.U D.affine) D.point =
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap C.algebra
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine ≫ φ) C.point := by
    rw [AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap_comp]
    exact D.point_eq.trans (congrArg (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) C.point_eq).symm
  have hder := congrArg (fun l : ModelX →L[ℂ] ModelY => l v) (C.mfderiv_charts φ D)
  have ht := JetOpenNaturality.regularChartSpecJet_schemeMap C.algebra D.algebra
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine ≫ φ)
    (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap Y D.U D.affine)
    C.chart D.chart C.regular D.regular C.point C.source D.point D.source hxy v
  exact (congrArg (fun w : ModelY => (D.tangentEquiv w).val) hder).trans
    ((D.tangentEquiv_jet _).trans (ht.trans
      ((Category.assoc _ _ _).symm.trans
        (congrArg (fun q : AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ ⟶ X => q ≫ φ) (C.tangentEquiv_jet v).symm))))

omit D in
theorem _root_.OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts.NativeTangentChart.tangentEquiv_naturality_of_point {q : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y}
    (D : Intrinsic.TangentCharts.NativeTangentChart Y q) (hpq : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ p = q) (v : ModelX) :
    (D.tangentEquiv
      (mfderiv 𝓘(ℂ, ModelX) 𝓘(ℂ, ModelY) (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map φ) p v)).val =
        (C.tangentEquiv v).val ≫ φ := by
  subst q
  exact C.tangentEquiv_naturality φ D v

end RepresentationTheory.Theta.Geometric.IntrinsicTangentNaturality.NativeTangentChart

namespace RepresentationTheory.Theta.Geometric

/-! The zero tangent is the constant infinitesimal point, for the literal
dual-number scaling map and the actual scheme base point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

theorem IntrinsicTangentNaturality.dualNumberScalar_zero :
    AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScalar ℂ 0 = toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberOrigin ℂ := by
  apply Over.OverMorphism.ext
  change Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale ℂ 0).toRingHom) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ))) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberReduction ℂ))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply TrivSqZeroExt.ext
  · change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale ℂ 0 z).fst =
      (algebraMap ℂ (DualNumber ℂ) z.fst).fst
    simp [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.algebraMap_eq_inl]
  · change (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale ℂ 0 z).snd = 0
    simp [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale]

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]

theorem Intrinsic.TangentCharts.NativeTangentChart.tangentEquiv_zero {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X} (C : Intrinsic.TangentCharts.NativeTangentChart X p) :
    (C.tangentEquiv 0).val = toUnit (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberTest ℂ) ≫ p := by
  have h := C.tangentEquiv_smul 0 0
  rw [zero_smul, IntrinsicTangentNaturality.dualNumberScalar_zero, Category.assoc,
    (C.tangentEquiv 0).property] at h
  exact h

theorem Intrinsic.TangentCharts.NativeTangentChart.tangentEquiv_zero_one [MonObj X] (C : Intrinsic.TangentCharts.NativeTangentChart X 1) :
    (C.tangentEquiv 0).val = 1 := by
  rw [C.tangentEquiv_zero, MonObj.comp_one]

end RepresentationTheory.Theta.Geometric

end

end OAI
