import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportRegularFunction

/-! # Generic Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GenericDimension.BundleCycles

noncomputable section

/-! # LineBundleCycles: actual finite generic field extensions preserve support dimension without requiring the scheme map to be finite -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem schemeDimension_eq_of_finiteGenericMap {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    (hfinite : letI := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
      Module.Finite Y.functionField X.functionField) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (f ≫ g) := by
  let := (Cycles.Functoriality.FunctionFields.Construction.genericFieldMap f hη).hom.toAlgebra
  let := hfinite
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra g
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (f ≫ g)
  let : IsScalarTower ℂ Y.functionField X.functionField :=
    IsScalarTower.of_algHom (Cycles.Functoriality.FunctionFields.Construction.genericFieldAlgHom f hη g)
  have h := trdeg_add_eq ℂ Y.functionField (A := X.functionField)
  rw [trdeg_eq_zero (R := Y.functionField) (A := X.functionField), add_zero] at h
  exact congrArg Cardinal.toNat h

theorem pointClosure_dimension_of_nonzeroResidueDegree {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (f : X ⟶ Y) (g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (x : X) (hx : f.residueDegree x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (f x)) g =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (f ≫ g) := by
  let r := Point.SupportMap.BundleCycles.pointSupportMap f x
  let hη := Point.SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x r (Point.SupportMap.BundleCycles.pointSupportMap_inclusion f x)
  let := (Point.SupportMap.BundleCycles.pointSupportFunctionFieldMap f x).hom.toAlgebra
  have hfinite : Module.Finite (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).functionField
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField := by
    apply Module.finite_of_finrank_pos
    rw [Point.SupportRegularFunction.BundleCycles.pointSupportFunctionFieldMap_finrank]
    exact Nat.pos_of_ne_zero hx
  have h := schemeDimension_eq_of_finiteGenericMap r hη hfinite
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap (irreducibleSetEquivPoints.symm (f x)) g)
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (CycleClass.Geometric.SupportFiniteType.supportStructureMap _ g) =
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (Point.SupportMap.BundleCycles.pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι _ ≫ g) at h
  rw [← Category.assoc, Point.SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc] at h
  exact h

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Finite.GenericDimension.BundleCycles
