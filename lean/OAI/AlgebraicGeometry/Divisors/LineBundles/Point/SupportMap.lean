import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportNaturality
import OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure

/-! # Support Map -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap.BundleCycles

noncomputable section

/-!
# LineBundleCycles: the actual induced map between reduced point closures

The image of the generic point determines the reduced image closure.
Factoring the original morphism through that image gives the required
map of supports and its commuting inclusion square.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)

theorem morphismPointSupport_imageClosure :
    CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ f) =
      irreducibleSetEquivPoints.symm (f x) := by
  apply IrreducibleCloseds.ext
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  have h := (genericPoint_spec (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))).image
    (i ≫ f).continuous
  have he := h.def
  simp only [Set.image_univ] at he
  change closure (Set.range (i ≫ f)) = closure {f x}
  have hp : (i ≫ f) (genericPoint _) = f x := congrArg f (SupportNaturality.BundleCycles.pointSupport_genericPoint X x)
  exact he.symm.trans (congrArg (fun y : Y => closure {y}) hp)

variable [AlgebraicGeometry.IsNoetherian X]

def pointSupportMap :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x) ⟶
      CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x)) := by
  apply IsClosedImmersion.lift (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)))
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ f)
  change (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm (f x))).subschemeι.ker ≤ _
  rw [Scheme.IdealSheafData.ker_subschemeι, CycleClass.Geometric.StratumClosure.kernel_eq_reducedImageClosureIdeal,
    morphismPointSupport_imageClosure f x]

theorem pointSupportMap_inclusion :
    pointSupportMap f x ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)) =
      CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ f :=
  IsClosedImmersion.lift_fac (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)))
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ f) _

def pointSupportFunctionFieldMap :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))).functionField ⟶
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).functionField :=
  Cycles.Functoriality.FunctionFields.Construction.genericFieldMap (pointSupportMap f x)
    (SupportNaturality.BundleCycles.pointSupportMap_genericPoint f x (pointSupportMap f x) (pointSupportMap_inclusion f x))

theorem pointSupportFunctionFieldMap_residue :
    (SupportResidue.BundleCycles.pointSupportResidueIso Y (f x)).hom ≫ pointSupportFunctionFieldMap f x =
      f.residueFieldMap x ≫ (SupportResidue.BundleCycles.pointSupportResidueIso X x).hom :=
  SupportNaturality.BundleCycles.pointSupportResidueIso_naturality f x (pointSupportMap f x) (pointSupportMap_inclusion f x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap.BundleCycles
