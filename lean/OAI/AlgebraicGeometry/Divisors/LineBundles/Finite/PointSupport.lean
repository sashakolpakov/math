import OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.FunctionFields
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization

/-! # Point Support -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PointSupport.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finite maps on actual point closures preserve support dimension
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem schemeDimension_eq_of_finite {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] (hη : f (genericPoint X) = genericPoint Y)
    (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := FunctionFields.BundleCycles.finiteMorphism_functionField_finite f hη
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ g)
  let : IsScalarTower ℂ Y.functionField X.functionField :=
    IsScalarTower.of_algHom (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom f hη g)
  have h := trdeg_add_eq ℂ Y.functionField (A := X.functionField)
  rw [trdeg_eq_zero (R := Y.functionField) (A := X.functionField), add_zero] at h
  exact congrArg Cardinal.toNat h

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsFinite i]

instance finitePointSupportMap_isFinite (x : X) : IsFinite (Point.SupportMap.BundleCycles.pointSupportMap i x) := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))
  have hc : IsFinite (Point.SupportMap.BundleCycles.pointSupportMap i x ≫ j) := by
    change IsFinite (Point.SupportMap.BundleCycles.pointSupportMap i x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x)))
    rw [Point.SupportMap.BundleCycles.pointSupportMap_inclusion]
    infer_instance
  exact IsFinite.of_comp (Point.SupportMap.BundleCycles.pointSupportMap i x) j

theorem pointClosure_dimension_finite (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) := by
  have h := schemeDimension_eq_of_finite (Point.SupportMap.BundleCycles.pointSupportMap i x)
    (Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint i x (Point.SupportMap.BundleCycles.pointSupportMap i x) (Point.SupportMap.BundleCycles.pointSupportMap_inclusion i x))
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm (i x)) f)
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap _ f) =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Point.SupportMap.BundleCycles.pointSupportMap i x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι _ ≫ f) at h
  rw [← Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.PointSupport.BundleCycles
