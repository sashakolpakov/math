import OAI.ArithmeticGeometry.Descent.CMVariety.ChartDensity
import OAI.ArithmeticGeometry.Descent.CMVariety.RationalEtaleCharts

/-! # Smooth Density -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety

noncomputable section

/-! Actual number-field points are dense in the native complex points of
every smooth rational scheme. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

theorem ChartDensity.Abelian.IsNumberFieldPoint.comp {X Y : Scheme} {p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X}
    (hp : ChartDensity.Abelian.IsNumberFieldPoint p) (f : X ⟶ Y) : ChartDensity.Abelian.IsNumberFieldPoint (p ≫ f) := by
  obtain ⟨K, hK, pK, h⟩ := hp
  exact ⟨K, hK, pK ≫ f, (Category.assoc _ _ _).symm.trans
    (congrArg (fun q : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X => q ≫ f) h)⟩

theorem SmoothDensity.Abelian.arithmeticComplexPoint_of_projection {X : Scheme}
    (f : X ⟶ Spec (CommRingCat.of ℚ))
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase f)) :
    ComplexParameter.Abelian.arithmeticComplexPoint f (ChartDensity.Abelian.arithmeticPointProjection f s) = s := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · exact ComplexParameter.Abelian.arithmeticComplexPoint_projection f (ChartDensity.Abelian.arithmeticPointProjection f s)
  · exact (ComplexParameter.Abelian.arithmeticComplexPoint f (ChartDensity.Abelian.arithmeticPointProjection f s)).w.trans s.w.symm

theorem SmoothDensity.Abelian.arithmeticPointProjection_map {X Y : Scheme}
    (fX : X ⟶ Spec (CommRingCat.of ℚ)) (fY : Y ⟶ Spec (CommRingCat.of ℚ))
    (u : X ⟶ Y) (hu : u ≫ fY = fX)
    (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase fX)) :
    ChartDensity.Abelian.arithmeticPointProjection fY (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (BaseChangeMaps.Abelian.arithmeticBaseChangeMap fX fY u hu) s) =
      ChartDensity.Abelian.arithmeticPointProjection fX s ≫ u := by
  change (s.left ≫ (BaseChangeMaps.Abelian.arithmeticBaseChangeMap fX fY u hu).left) ≫ _ = (s.left ≫ _) ≫ u
  rw [Category.assoc, BaseChangeMaps.Abelian.arithmeticBaseChangeMap_fst, ← Category.assoc]

theorem SmoothDensity.Abelian.smooth_rational_scheme_numberField_points_dense
    {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℚ)) [Smooth f] :
    Dense {s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints (ComplexParameter.Abelian.arithmeticComplexBase f) |
      ChartDensity.Abelian.IsNumberFieldPoint (ChartDensity.Abelian.arithmeticPointProjection f s)} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨s, hs⟩ := hne
  obtain ⟨Y, q, j, y, n, u, _, hu, hqf, hjq, hyj, huq⟩ :=
    RationalEtaleCharts.Abelian.smooth_point_has_rational_etale_neighborhood f (ChartDensity.Abelian.arithmeticPointProjection f s)
  have : Etale u := hu
  have : LocallyQuasiFinite u := hqf
  let v := BaseChangeMaps.Abelian.arithmeticBaseChangeMap q f j hjq
  let t := ComplexParameter.Abelian.arithmeticComplexPoint q y
  have ht : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v t = s :=
    (BaseChangeMaps.Abelian.arithmeticBaseChangeMap_point q f j hjq y (ChartDensity.Abelian.arithmeticPointProjection f s) hyj).trans
      (SmoothDensity.Abelian.arithmeticComplexPoint_of_projection f s)
  have hpre : IsOpen ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v) ⁻¹' U) :=
    hU.preimage (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map v)
  have hnonempty : ((AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v) ⁻¹' U).Nonempty := by
    refine ⟨t, ?_⟩
    change AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v t ∈ U
    rwa [ht]
  obtain ⟨z, hzU, hz⟩ := (ChartDensity.Abelian.arithmetic_chart_numberField_points_dense q n u huq).inter_open_nonempty
    _ hpre hnonempty
  refine ⟨AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v z, hzU, ?_⟩
  change ChartDensity.Abelian.IsNumberFieldPoint (ChartDensity.Abelian.arithmeticPointProjection f (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map v z))
  rw [SmoothDensity.Abelian.arithmeticPointProjection_map]
  exact hz.comp j

end

end OAI.ArithmeticGeometry.Descent.CMVariety
