import OAI.ArithmeticGeometry.Descent.CMVariety.RelativePointOpenness
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood
import OAI.ArithmeticGeometry.Descent.CMVariety.AffineFamilyNeighborhood
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection

/-! # Smooth Intrinsic Point Map -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.SmoothIntrinsicPointMap.Abelian.RelativeCharts

noncomputable section

/-! Smooth scheme morphisms over smooth complex bases induce open maps
on the actual native complex-point spaces. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set Filter
open scoped _root_.Topology Classical

theorem smooth_native_diagram_image_mem_nhds
    {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} (p : X ⟶ S) [Smooth p.left]
    {R A : Type} [CommRing R] [Algebra ℂ R]
    [CommRing A] [Algebra ℂ A] [Algebra R A] [IsScalarTower ℂ R A]
    (b : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ R ⟶ S) [IsOpenImmersion b.left]
    (i : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ A ⟶ X) [IsOpenImmersion i.left]
    (hi : i ≫ p = AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ R A (IsScalarTower.toAlgHom ℂ R A) ≫ b)
    (P : LocalizedSectionCharts.Abelian.RelativeCharts.ComplexPresentation R) (x : AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineComplexPoints A)
    {U : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)}
    (hU : U ∈ 𝓝 (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x)) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p '' U ∈
      𝓝 (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p
        (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i x)) := by
  let : Algebra.Smooth R A := FiberChartProjection.Abelian.RelativeCharts.algebraSmooth_of_nativeDiagram p b i hi
  have hpre := (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_affinePointMap (CommAlgCat.of ℂ A) i).continuousAt.preimage_mem_nhds hU
  have himage := RelativePointOpenness.Abelian.RelativeCharts.smooth_affine_point_image_mem_nhds P.presentation x hpre
  have hbase := (AlgebraicGeometry.ComplexPoints.Analytic.SmoothSchemeManifold.isOpenEmbedding_affinePointMap (CommAlgCat.of ℂ R) b).isOpenMap.image_mem_nhds himage
  rw [← FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base p b i hi x] at hbase
  apply mem_of_superset hbase
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affinePointMap (CommAlgCat.of ℂ A) i y,
    hy, FiberChartProjection.Abelian.RelativeCharts.nativeAffinePoint_base p b i hi y⟩

theorem smooth_native_point_image_mem_nhds
    {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom]
    (p : X ⟶ S) [Smooth p.left] (t : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)
    {U : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X)} (hU : U ∈ 𝓝 t) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p '' U ∈ 𝓝 (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p t) := by
  obtain ⟨R, b, hb, y, P, hy⟩ := SmoothBaseNeighborhood.Abelian.RelativeCharts.exists_smooth_affine_base_neighborhood S (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p t)
  let : IsOpenImmersion b.left := hb
  have ht : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p t ∈ Set.range (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map b) :=
    ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv R y, hy⟩
  obtain ⟨A, a, tower, i, hI, hi, hx⟩ := AffineFamilyNeighborhood.Abelian.RelativeCharts.exists_affine_diagram_over_open p b t ht
  let : Algebra R A := a
  let : IsScalarTower ℂ R A := tower
  let : IsOpenImmersion i.left := hI
  obtain ⟨x, rfl⟩ := hx
  exact smooth_native_diagram_image_mem_nhds p b i hi P x hU

theorem isOpenMap_smooth_native_point_map
    {X S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth S.hom]
    (p : X ⟶ S) [Smooth p.left] : IsOpenMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map p) := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨t, ht, rfl⟩
  exact smooth_native_point_image_mem_nhds p t (hU.mem_nhds ht)

end

end OAI.ArithmeticGeometry.Descent.CMVariety.SmoothIntrinsicPointMap.Abelian.RelativeCharts
