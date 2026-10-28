import OAI.ArithmeticGeometry.Descent.CMVariety.ComplexParameter
import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothIntrinsicPointMap
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons

/-! # Base Change Maps -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMaps.Abelian

noncomputable section

/-! Native complex base-change maps for actual commuting arithmetic diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

def arithmeticBaseChangeMap
    {X Y : Scheme} (fX : X ⟶ Spec (CommRingCat.of ℚ)) (fY : Y ⟶ Spec (CommRingCat.of ℚ))
    (u : X ⟶ Y) (hu : u ≫ fY = fX) : ComplexParameter.Abelian.arithmeticComplexBase fX ⟶ ComplexParameter.Abelian.arithmeticComplexBase fY :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))).map
    (Over.homMk u hu : Over.mk fX ⟶ Over.mk fY)

theorem arithmeticBaseChangeMap_fst
    {X Y : Scheme} (fX : X ⟶ Spec (CommRingCat.of ℚ)) (fY : Y ⟶ Spec (CommRingCat.of ℚ))
    (u : X ⟶ Y) (hu : u ≫ fY = fX) :
    (arithmeticBaseChangeMap fX fY u hu).left ≫
      pullback.fst fY (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) =
    pullback.fst fX (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))) ≫ u :=
  AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.Comparisons.overPullback_map_left_fst (Over.homMk u hu : Over.mk fX ⟶ Over.mk fY) _

instance arithmeticBaseChangeMap_smooth
    {X Y : Scheme} (fX : X ⟶ Spec (CommRingCat.of ℚ)) (fY : Y ⟶ Spec (CommRingCat.of ℚ))
    (u : X ⟶ Y) (hu : u ≫ fY = fX) [Smooth u] :
    Smooth (arithmeticBaseChangeMap fX fY u hu).left :=
  MorphismProperty.overPullbackMap (P := @Smooth)
    (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))
    (Over.homMk u hu : Over.mk fX ⟶ Over.mk fY) (inferInstanceAs (Smooth u))

theorem arithmeticBaseChangeMap_point
    {X Y : Scheme} (fX : X ⟶ Spec (CommRingCat.of ℚ)) (fY : Y ⟶ Spec (CommRingCat.of ℚ))
    (u : X ⟶ Y) (hu : u ≫ fY = fX)
    (p : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ X) (q : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ Y) (hp : p ≫ u = q) :
    AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (arithmeticBaseChangeMap fX fY u hu) (ComplexParameter.Abelian.arithmeticComplexPoint fX p) =
      ComplexParameter.Abelian.arithmeticComplexPoint fY q := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ))
  let a : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ pullback fX c := (ComplexParameter.Abelian.arithmeticComplexPoint fX p).left
  let b : AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase ⟶ pullback fY c := (ComplexParameter.Abelian.arithmeticComplexPoint fY q).left
  let v : pullback fX c ⟶ pullback fY c := (arithmeticBaseChangeMap fX fY u hu).left
  have hva : v ≫ pullback.fst fY c = pullback.fst fX c ≫ u := arithmeticBaseChangeMap_fst fX fY u hu
  have ha : a ≫ pullback.fst fX c = p := ComplexParameter.Abelian.arithmeticComplexPoint_projection fX p
  have hb : b ≫ pullback.fst fY c = q := ComplexParameter.Abelian.arithmeticComplexPoint_projection fY q
  apply Over.OverMorphism.ext
  change a ≫ v = b
  apply pullback.hom_ext
  · rw [Category.assoc, hva, ← Category.assoc, ha, hp, hb]
  · exact (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (arithmeticBaseChangeMap fX fY u hu)
      (ComplexParameter.Abelian.arithmeticComplexPoint fX p)).w.trans (ComplexParameter.Abelian.arithmeticComplexPoint fY q).w.symm

theorem arithmeticBaseChangeMap_isOpenMap
    {X Y : Scheme} (fX : X ⟶ Spec (CommRingCat.of ℚ)) (fY : Y ⟶ Spec (CommRingCat.of ℚ))
    (u : X ⟶ Y) (hu : u ≫ fY = fX) [Smooth fY] [Smooth u] :
    IsOpenMap (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.map (arithmeticBaseChangeMap fX fY u hu)) := by
  let : Smooth (ComplexParameter.Abelian.arithmeticComplexBase fY).hom :=
    inferInstanceAs (Smooth (pullback.snd fY (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℂ)))))
  exact SmoothIntrinsicPointMap.Abelian.RelativeCharts.isOpenMap_smooth_native_point_map _

end

end OAI.ArithmeticGeometry.Descent.CMVariety.BaseChangeMaps.Abelian
