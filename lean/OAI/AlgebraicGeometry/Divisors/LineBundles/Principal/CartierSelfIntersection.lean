import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber

/-! # Cartier Self Intersection -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierSelfIntersection.BundleCycles

noncomputable section

/-!
# LineBundleCycles: zero self-intersection for a global principal equation

If a reduced integral support lies in the zero locus, the restricted
regular section is actually zero. Thus the principal intersection cycle
of a cycle already supported on the fiber is zero. This proves the
cycle-level independence from adding closed-fiber cycles.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X]

omit [AlgebraicGeometry.IsNoetherian X] in
/-- A section vanishing on every point of a reduced support is the zero section there. -/
theorem supportRegularFunction_eq_zero (a : Γ(X, ⊤)) (W : IrreducibleCloseds X)
    (hW : (W : Set X) ⊆ (X.basicOpen a : Set X)ᶜ) : CartierCycle.BundleCycles.supportRegularFunction a W = 0 := by
  have hsection : (CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop a = 0 := by
    apply eq_zero_of_basicOpen_eq_bot
    apply le_antisymm _ bot_le
    intro y hy
    have hpre := Scheme.preimage_basicOpen_top (CycleClass.Geometric.GenericPoint.reducedSupportι W) a
    have hya : CycleClass.Geometric.GenericPoint.reducedSupportι W y ∈ X.basicOpen a :=
      (congrArg (fun U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens => y ∈ U) hpre).mpr hy
    have hyW : CycleClass.Geometric.GenericPoint.reducedSupportι W y ∈ (W : Set X) := by
      rw [← CycleClass.Geometric.GenericPoint.range_reducedSupportι]
      exact ⟨y, rfl⟩
    exact (hW hyW hya).elim
  change (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).germToFunctionField ⊤ ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop a) = 0
  rw [hsection, map_zero]

variable {Z : Scheme} (j : Z ⟶ X) [IsClosedImmersion j] (a : Γ(X, ⊤))
    (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

include hzero

theorem principalCartierGradedCycle_closed (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) (d + 1)) :
    CartierFiber.BundleCycles.principalCartierGradedCycle a f d (Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f (d + 1) x) = 0 := by
  have hW : (irreducibleSetEquivPoints.symm (j x.1) : Set X) ⊆ (X.basicOpen a : Set X)ᶜ := by
    have hr : closure {j x.1} ⊆ Set.range j :=
      j.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr ⟨x.1, rfl⟩)
    intro y hy
    exact (congrArg (fun s : Set X => y ∈ s) hzero).mp (hr hy)
  have hz := supportRegularFunction_eq_zero a (irreducibleSetEquivPoints.symm (j x.1)) hW
  exact (congrArg (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (irreducibleSetEquivPoints.symm (j x.1))) hz).trans
    (CartierCycle.BundleCycles.schemeGradedPrincipalDivisor_zero f d (irreducibleSetEquivPoints.symm (j x.1)))

theorem principalCartierFiberCycle_closed (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) (d + 1)) :
    CartierFiber.BundleCycles.principalCartierFiberCycle j a f d (Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f (d + 1) x) = 0 :=
  (congrArg (Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift j f d) (principalCartierGradedCycle_closed j a hzero f d x)).trans
    (map_zero (Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift j f d))

/-- Adding any cycle pushed from the closed zero fiber does not change the intersection cycle. -/
theorem principalCartierFiberCycleMap_closed (d : ℕ) :
    (CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d).comp (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f (d + 1)) = 0 := by
  apply Finsupp.lhom_ext
  intro x q
  change CartierFiber.BundleCycles.principalCartierFiberCycleMap j a f d (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f (d + 1) (Finsupp.single x q)) = 0
  rw [Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward_single]
  change Finsupp.linearCombination ℚ (CartierFiber.BundleCycles.principalCartierFiberCycle j a f d)
    (Finsupp.single (Closed.CyclePushforward.BundleCycles.closedDimensionPointMap j f (d + 1) x) q) = 0
  rw [Finsupp.linearCombination_single, principalCartierFiberCycle_closed j a hzero f d, smul_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierSelfIntersection.BundleCycles
