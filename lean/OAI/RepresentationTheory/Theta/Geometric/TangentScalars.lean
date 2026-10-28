import OAI.RepresentationTheory.Theta.Geometric.ExtendedComplexPoints
import OAI.RepresentationTheory.Theta.Geometric.ChartTangents
import OAI.RepresentationTheory.Theta.Geometric.Intrinsic.TangentCharts
import OAI.RepresentationTheory.Theta.Geometric.PointCharts

/-! # Tangent Scalars -/

namespace OAI.RepresentationTheory.Theta.Geometric

noncomputable section

section

/-! Every tangent point of the original smooth complex scheme over an
extended residue field is obtained from the scalar-extended native chart. -/

open scoped TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X} (C : Intrinsic.TangentCharts.NativeTangentChart X p)
  (F : Type) [Field F] [Algebra ℂ F]

def Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv :
    (F ⊗[ℂ] (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) ≃
      TangentSources.extendedSchemeTangentPoints ℂ F X (ExtendedComplexPoints.extendedComplexPoint F p) := by
  have hp : ExtendedComplexPoints.extendedComplexPoint F (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C.algebra C.point) ≫
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine = ExtendedComplexPoints.extendedComplexPoint F p := by
    change (toUnit _ ≫ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.affineSchemePointEquiv C.algebra C.point) ≫
      AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine = toUnit _ ≫ p
    rw [Category.assoc]
    exact congrArg (fun z : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X =>
      toUnit ((Over.map (LieFieldTests.fieldBaseMap ℂ F)).obj (Over.mk (𝟙 (Spec (.of F))))) ≫ z) C.point_eq
  exact ((PointCharts.pointChartGeometricEquiv F C.chart C.regular C.point C.source).trans
    (TangentSources.extendedTangentNeighborhoodEquiv ℂ F X _
      (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine) _)).trans
        (Equiv.subtypeEquivRight (fun _ => by rw [hp]))

theorem Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv_pointChart
    (z : F ⊗[ℂ] (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) :
    (C.geometricTangentEquiv F z).val =
      (PointCharts.pointChartGeometricEquiv F C.chart C.regular C.point C.source z).val ≫
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine := rfl

theorem Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv_apply
    (z : F ⊗[ℂ] (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) :
    let xF : C.algebra →ₐ[ℂ] F := (Algebra.ofId ℂ F).comp C.point
    letI : Algebra C.algebra F := xF.toRingHom.toAlgebra
    letI : IsScalarTower ℂ C.algebra F := IsScalarTower.of_algHom xF
    letI : IsScalarTower C.algebra ℂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    (C.geometricTangentEquiv F z).val =
      ((TangentSources.geometricDualNumberIso ℂ F).inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C.algebra (DualNumber F)
        (DualNumbers.geometricDerivationJet
          (ChartTangents.geometricChartDerivation F C.chart C.regular C.point C.source (fun _ => rfl) z))) ≫
        AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine := by
  rw [C.geometricTangentEquiv_pointChart]
  exact congrArg (fun t : LieFieldTests.extendedDualTest ℂ F ⟶ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineSchemeOver ℂ C.algebra =>
    t ≫ AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.affineOpenSchemeMap X C.U C.affine)
      (PointCharts.pointChartGeometricEquiv_apply F C.chart C.regular C.point C.source z)

end

/-! The scalar action after residue-field extension is precisely the
native scaling morphism of that field's dual-number test scheme. -/

open scoped TensorProduct
open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {k A F : Type} [Field k] [CommRing A] [Field F]
  [Algebra k A] [Algebra k F] [Algebra A F] [IsScalarTower k A F]

theorem TangentScalars.geometricDerivationJet_smul (c : F) (δ : Derivation k A F) :
    DualNumbers.geometricDerivationJet (c • δ) =
      ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale F c).restrictScalars k).comp (DualNumbers.geometricDerivationJet δ) := by
  apply AlgHom.ext
  intro a
  apply TrivSqZeroExt.ext
  · exact (TrivSqZeroExt.fst_map _ _).symm
  · change c • δ a = (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale F c (DualNumbers.geometricDerivationJet δ a)).snd
    rw [AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale, TrivSqZeroExt.snd_map]
    rfl

omit A [CommRing A] [Algebra k A] [Algebra A F] [IsScalarTower k A F] in
theorem TangentScalars.nativeExtendedDualScalar (c : F) :
    (TangentSources.geometricDualNumberIso k F).inv ≫
      AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv k (DualNumber F) (DualNumber F)
        ((AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale F c).restrictScalars k) =
      LieFieldTests.extendedDualScalar k F c ≫ (TangentSources.geometricDualNumberIso k F).inv := by
  apply Over.OverMorphism.ext
  change 𝟙 (Spec (.of (DualNumber F))) ≫
      Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale F c).toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgebraicGeometry.AbelianModuli.ReferenceFamily.LieRanks.dualNumberScale F c).toRingHom) ≫ 𝟙 (Spec (.of (DualNumber F)))
  simp only [Category.id_comp, Category.comp_id]

variable {X : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase} [IsIntegral X.left] [Smooth X.hom]
  {p : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X} (C : Intrinsic.TangentCharts.NativeTangentChart X p)
  (F : Type) [Field F] [Algebra ℂ F]

theorem Intrinsic.TangentCharts.NativeTangentChart.geometricTangentEquiv_smul (c : F)
    (z : F ⊗[ℂ] (Fin (AlgebraicGeometry.Betti.AffineDimension.Realization.functionFieldDifferentialDimension X.hom) → ℂ)) :
    (C.geometricTangentEquiv F (c • z)).val =
      LieFieldTests.extendedDualScalar ℂ F c ≫ (C.geometricTangentEquiv F z).val := by
  let xF : C.algebra →ₐ[ℂ] F := (Algebra.ofId ℂ F).comp C.point
  let : Algebra C.algebra F := xF.toRingHom.toAlgebra
  let : IsScalarTower ℂ C.algebra F := IsScalarTower.of_algHom xF
  let : IsScalarTower C.algebra ℂ F := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hd := (ChartTangents.geometricChartDerivation F C.chart C.regular C.point C.source (fun _ => rfl)).map_smul c z
  have hj := (congrArg (fun δ : Derivation ℂ C.algebra F => DualNumbers.geometricDerivationJet δ) hd).trans
    (TangentScalars.geometricDerivationJet_smul c
      (ChartTangents.geometricChartDerivation F C.chart C.regular C.point C.source (fun _ => rfl) z))
  rw [C.geometricTangentEquiv_apply, C.geometricTangentEquiv_apply]
  change ((TangentSources.geometricDualNumberIso ℂ F).inv ≫ AlgebraicGeometry.Foundations.Scheme.AffineComplexPoints.affineAlgHomOverSpecEquiv ℂ C.algebra (DualNumber F)
    (DualNumbers.geometricDerivationJet (ChartTangents.geometricChartDerivation F C.chart C.regular C.point C.source
      (fun _ => rfl) (c • z)))) ≫ _ = _
  rw [hj, ← Affine.Tangents.affineSpec_comp, ← Category.assoc (TangentSources.geometricDualNumberIso ℂ F).inv,
    TangentScalars.nativeExtendedDualScalar]
  simp only [Category.assoc]

end

end OAI.RepresentationTheory.Theta.Geometric
