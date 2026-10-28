import OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportMap
import OAI.AlgebraicGeometry.Divisors.LineBundles.Open.SupportGenericPoint

/-! # Support Open Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenCycle.BundleCycles

noncomputable section

section

/-! # LineBundleCycles: the actual induced map of prime supports under an open immersion is an open immersion -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

theorem reducedSupportι_eqToHom {X : Scheme.{0}} {W V : IrreducibleCloseds X} (h : W = V) :
    eqToHom (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme h) ≫ CycleClass.Geometric.GenericPoint.reducedSupportι V = CycleClass.Geometric.GenericPoint.reducedSupportι W := by
  subst V
  simp

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsOpenImmersion i] (x : X)

theorem pointSupportMap_open_factorization :
    SupportMap.BundleCycles.pointSupportMap i x =
      eqToHom (congrArg CycleClass.Geometric.GenericPoint.reducedSupportScheme (Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure i x).symm) ≫
        Open.SupportRestriction.BundleCycles.openRestrictedSupportMap i (irreducibleSetEquivPoints.symm (i x)) := by
  apply (cancel_mono (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x)))).mp
  rw [SupportMap.BundleCycles.pointSupportMap_inclusion, Category.assoc, Open.SupportRestriction.BundleCycles.openRestrictedSupportMap_inclusion,
    ← Category.assoc, reducedSupportι_eqToHom]
  exact (Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure i x).symm

instance pointSupportMap_open_isOpenImmersion : IsOpenImmersion (SupportMap.BundleCycles.pointSupportMap i x) := by
  rw [pointSupportMap_open_factorization i x]
  infer_instance

instance pointSupportFunctionFieldMap_open_isIso : IsIso (SupportMap.BundleCycles.pointSupportFunctionFieldMap i x) :=
  inferInstanceAs (IsIso (RationalDivisorRestriction.BundleCycles.openFunctionFieldMap (SupportMap.BundleCycles.pointSupportMap i x)))

omit [IsOpenImmersion i] in
theorem pointSupportMap_open_preimage (U : Y.Opens) :
    (SupportMap.BundleCycles.pointSupportMap i x) ⁻¹ᵁ ((CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))) ⁻¹ᵁ U) =
      (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) ⁻¹ᵁ (i ⁻¹ᵁ U) :=
  congrArg (fun f => f ⁻¹ᵁ U) (SupportMap.BundleCycles.pointSupportMap_inclusion i x)

end

/-! # LineBundleCycles: open restriction commutes with the actual cycle inclusion from a prime support -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsOpenImmersion i] (x : X)

theorem pointSupportOpen_pointCycle
    (z : CycleClass.Geometric.GenericPoint.reducedSupportScheme (irreducibleSetEquivPoints.symm (i x)) →₀ ℚ) :
    Finsupp.comapDomain i
        (Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))) z)
        i.isOpenEmbedding.injective.injOn =
      Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))
        (Finsupp.comapDomain (SupportMap.BundleCycles.pointSupportMap i x) z (SupportMap.BundleCycles.pointSupportMap i x).isOpenEmbedding.injective.injOn) := by
  ext y
  by_cases hy : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))
  · obtain ⟨w, rfl⟩ := hy
    have hp := congrArg (fun f => f w) (SupportMap.BundleCycles.pointSupportMap_inclusion i x)
    change CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x)) (SupportMap.BundleCycles.pointSupportMap i x w) =
      i (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) w) at hp
    change Finsupp.mapDomain (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))) z
      (i (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) w)) = _
    rw [← hp,
      Finsupp.mapDomain_apply_of_injective (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))).isClosedEmbedding.injective,
      Finsupp.mapDomain_apply_of_injective (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)).isClosedEmbedding.injective]
    rfl
  · have hi : i y ∉ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm (i x))) := by
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      intro h
      apply hy
      rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι, ← Open.SupportGenericPoint.BundleCycles.openRestrictedSupport_pointClosure i x, Open.SupportRestriction.BundleCycles.openRestrictedSupport_coe]
      exact h
    exact (Finsupp.mapDomain_of_notMem_range _ _ hi).trans
      (Finsupp.mapDomain_of_notMem_range _ _ hy).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Point.SupportOpenCycle.BundleCycles
