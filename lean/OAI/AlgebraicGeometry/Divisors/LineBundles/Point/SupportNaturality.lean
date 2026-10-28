import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidue
import OAI.AlgebraicGeometry.Divisors.LineBundles.ResidueFieldSquare

/-! # Support Naturality -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportNaturality.BundleCycles

noncomputable section

/-!
# LineBundleCycles: naturality of the actual residue-field/prime-support identification

An actual commuting map of reduced point closures induces the same
field map as the ambient residue-field map. All point identifications
come from their actual generic points.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

theorem pointSupport_genericPoint (X : Scheme.{u}) (x : X) :
    CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
      (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))) = x :=
  (CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq _).trans (irreducibleSetEquivPoints.apply_symm_apply x)

theorem pointSupportResidueIso_comp_genericResidue (X : Scheme.{u}) (x : X) :
    (SupportResidue.BundleCycles.pointSupportResidueIso X x).hom ≫
      (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))).hom =
      (X.residueFieldCongr (pointSupport_genericPoint X x).symm).hom ≫
        (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).residueFieldMap
          (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x))) := by
  simp only [SupportResidue.BundleCycles.pointSupportResidueIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks_hom]

theorem pointSupportMap_genericPoint {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (r : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x) ⟶
      CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x)))
    (hr : r ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)) =
      CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ f) :
    r (genericPoint _) = genericPoint _ := by
  apply (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))).isClosedEmbedding.injective
  calc
    CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)) (r (genericPoint _)) =
        f (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) (genericPoint _)) :=
      congrArg (fun j => j (genericPoint _)) hr
    _ = f x := congrArg f (pointSupport_genericPoint X x)
    _ = CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)) (genericPoint _) :=
      (pointSupport_genericPoint Y (f x)).symm

theorem pointSupportResidueIso_naturality {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (r : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x) ⟶
      CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x)))
    (hr : r ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x)) =
      CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ f) :
    (SupportResidue.BundleCycles.pointSupportResidueIso Y (f x)).hom ≫
      Cycles.Functoriality.FunctionFields.Construction.genericFieldMap r (pointSupportMap_genericPoint f x r hr) =
      f.residueFieldMap x ≫ (SupportResidue.BundleCycles.pointSupportResidueIso X x).hom := by
  let A := CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)
  let B := CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (f x))
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (f x))
  let hη := pointSupportMap_genericPoint f x r hr
  have hs := ResidueFieldSquare.BundleCycles.residueFieldMap_point_square i j f r hr (genericPoint A) (genericPoint B) x
    (pointSupport_genericPoint X x) (pointSupport_genericPoint Y (f x)) hη
  apply (cancel_mono (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso A).hom).mp
  calc
    ((SupportResidue.BundleCycles.pointSupportResidueIso Y (f x)).hom ≫ Cycles.Functoriality.FunctionFields.Construction.genericFieldMap r hη) ≫
        (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso A).hom =
      (SupportResidue.BundleCycles.pointSupportResidueIso Y (f x)).hom ≫
        ((Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso B).hom ≫ (B.residueFieldCongr hη.symm).hom ≫
          r.residueFieldMap (genericPoint A)) := by
      rw [Category.assoc, Cycles.Functoriality.ResidueDegree.Construction.genericFieldMap_residue_square r hη]
    _ = ((Y.residueFieldCongr (pointSupport_genericPoint Y (f x)).symm).hom ≫
        j.residueFieldMap (genericPoint B)) ≫
        ((B.residueFieldCongr hη.symm).hom ≫ r.residueFieldMap (genericPoint A)) := by
      rw [← Category.assoc, pointSupportResidueIso_comp_genericResidue Y (f x)]
    _ = f.residueFieldMap x ≫ (X.residueFieldCongr (pointSupport_genericPoint X x).symm).hom ≫
        i.residueFieldMap (genericPoint A) := (Category.assoc _ _ _).trans hs
    _ = (f.residueFieldMap x ≫ (SupportResidue.BundleCycles.pointSupportResidueIso X x).hom) ≫
        (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso A).hom := by
      rw [Category.assoc, pointSupportResidueIso_comp_genericResidue X x]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportNaturality.BundleCycles
