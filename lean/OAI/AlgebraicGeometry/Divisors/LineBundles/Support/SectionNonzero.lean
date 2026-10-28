import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.ChowLocalization

/-! # Section Nonzero -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.SectionNonzero.BundleCycles

noncomputable section

/-! A parent support whose generic point lies in the actual parameter nonvanishing open has a nonzero restricted rational section. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace

theorem supportRegularFunction_ne_zero_of_generic_basicOpen {X : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (s : Γ(X, ⊤)) (W : IrreducibleCloseds X) (hW : irreducibleSetEquivPoints W ∈ X.basicOpen s) :
    Principal.CartierCycle.BundleCycles.supportRegularFunction s W ≠ 0 := by
  have hpre := Scheme.preimage_basicOpen_top (CycleClass.Geometric.GenericPoint.reducedSupportι W) s
  have hη : genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ∈ (CycleClass.Geometric.GenericPoint.reducedSupportι W) ⁻¹ᵁ X.basicOpen s := by
    change CycleClass.Geometric.GenericPoint.reducedSupportι W (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) ∈ X.basicOpen s
    rw [CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_eq]
    exact hW
  rw [hpre, (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).mem_basicOpen _ _ (Opens.mem_top _)] at hη
  exact hη.ne_zero

theorem supportRegularFunction_pointClosure_ne_zero {X U : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (j : U ⟶ X) (s : Γ(X, ⊤)) (hj : Set.range j ⊆ X.basicOpen s) (x : U) :
    Principal.CartierCycle.BundleCycles.supportRegularFunction s (irreducibleSetEquivPoints.symm (j x)) ≠ 0 :=
  supportRegularFunction_ne_zero_of_generic_basicOpen s _
    (by rw [OrderIso.apply_symm_apply]; exact hj (Set.mem_range_self x))

theorem deformationPuncturedClosure_parameter_ne_zero {X : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (x : Deformation.ChowLocalization.BundleCycles.globalDeformationPunctured I) :
    Principal.CartierCycle.BundleCycles.supportRegularFunction (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
      (irreducibleSetEquivPoints.symm (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I x)) ≠ 0 :=
  supportRegularFunction_pointClosure_ne_zero (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedInclusion I)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection I) (by
      change Set.range (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).ι ⊆ Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I
      exact (Deformation.ChowLocalization.BundleCycles.globalDeformationPuncturedOpen I).range_ι.subset) x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.SectionNonzero.BundleCycles
