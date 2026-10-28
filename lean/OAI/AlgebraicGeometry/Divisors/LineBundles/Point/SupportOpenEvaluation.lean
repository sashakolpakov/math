import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportResidueEvaluation
import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportNaturality

/-! # Support Open Evaluation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenEvaluation.BundleCycles

noncomputable section

/-! # LineBundleCycles: evaluation on an arbitrary actual open agrees with restriction to a prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme.{0})

theorem pointSupportPreimage_nonempty (x : X) (U : X.Opens) (hxU : x ∈ U) :
    Nonempty ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)), ?_⟩⟩
  change CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) (genericPoint _) ∈ U
  rw [SupportNaturality.BundleCycles.pointSupport_genericPoint]
  exact hxU

theorem residueFieldCongr_openEvaluation {x y : X} (h : x = y) (U : X.Opens)
    (hxU : x ∈ U) (a : Γ(X, U)) :
    (X.residueFieldCongr h).hom (X.evaluation U x hxU a) = X.evaluation U y (h ▸ hxU) a := by
  subst y
  rfl

theorem pointSupportResidueIso_openEvaluation (x : X) (U : X.Opens) (hxU : x ∈ U) (a : Γ(X, U)) :
    letI := pointSupportPreimage_nonempty X x U hxU
    (SupportResidue.BundleCycles.pointSupportResidueIso X x).hom (X.evaluation U x hxU a) =
      (CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm x)).germToFunctionField
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ U)
        ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).app U a) := by
  let := pointSupportPreimage_nonempty X x U hxU
  let W := irreducibleSetEquivPoints.symm x
  let Z := CycleClass.Geometric.GenericPoint.reducedSupportScheme W
  let i := CycleClass.Geometric.GenericPoint.reducedSupportι W
  have hx : i (genericPoint Z) = x := SupportNaturality.BundleCycles.pointSupport_genericPoint X x
  change (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso Z).inv
      ((Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks i (genericPoint Z)).hom
        ((X.residueFieldCongr hx.symm).hom (X.evaluation U x hxU a))) = _
  rw [residueFieldCongr_openEvaluation, Foundations.Scheme.ImmersionComplexPoints.residueFieldIsoOfSurjectiveOnStalks_hom,
    Scheme.evaluation_naturality_apply]
  have he : Z.evaluation (i ⁻¹ᵁ U) (genericPoint Z) (show i (genericPoint Z) ∈ U from hx.symm ▸ hxU) (i.app U a) =
      (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso Z).hom (Z.germToFunctionField (i ⁻¹ᵁ U) (i.app U a)) := rfl
  rw [he]
  exact ConcreteCategory.congr_hom (Cycles.Functoriality.ResidueDegree.Construction.functionFieldResidueIso Z).hom_inv_id _

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenEvaluation.BundleCycles
