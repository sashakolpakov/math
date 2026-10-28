import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ResidueBoundary

/-! # Unit -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.Unit.BundleCycles

noncomputable section

/-!
# LineBundleCycles: global units give zero actual Cartier and residue cycles

A global unit restricts to a unit on every support and at every stalk.
Its complete principal divisor and Cartier operation vanish. Pairing
that unit with any nonzero rational function also has zero residue cycle.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable (X : Scheme) [AlgebraicGeometry.IsNoetherian X]

theorem principalDivisor_globalUnit [IsIntegral X] (a : Γ(X, ⊤)) (ha : IsUnit a) :
    Ord.BundleCycles.principalDivisor X (RegularDivisor.BundleCycles.globalFunctionFieldElement X a) = 0 := by
  ext x
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_eq_zero_of_isUnit_germ X a x (ha.map (X.presheaf.germ ⊤ x (by trivial)).hom)

theorem principalCartierPointCycle_globalUnit (a : Γ(X, ⊤)) (ha : IsUnit a) (W : IrreducibleCloseds X) :
    Principal.CartierCycle.BundleCycles.principalCartierPointCycle a W = 0 := by
  unfold Principal.CartierCycle.BundleCycles.principalCartierPointCycle Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor Principal.CartierCycle.BundleCycles.supportRegularFunction
  rw [principalDivisor_globalUnit (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) _ (ha.map (CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop.hom),
    Finsupp.mapRange_zero, Finsupp.embDomain_zero]

theorem principalCartierPointMap_globalUnit (a : Γ(X, ⊤)) (ha : IsUnit a) :
    Principal.CartierFiber.BundleCycles.principalCartierPointMap a = 0 := by
  apply Finsupp.lhom_ext
  intro x q
  rw [Principal.CartierFiber.BundleCycles.principalCartierPointMap_single, principalCartierPointCycle_globalUnit X a ha, smul_zero]
  rfl

theorem normalResidueBoundaryCycle_globalUnit [IsIntegral X]
    (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (a : Γ(X, ⊤)) (ha : IsUnit a)
    (g h : X.functionFieldˣ) (hg : (g : X.functionField) = RegularDivisor.BundleCycles.globalFunctionFieldElement X a) :
    Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle X hNormal g h = 0 := by
  unfold Normal.PointResidue.BundleCycles.normalResidueBoundaryCycle
  apply Finset.sum_eq_zero
  intro x _
  let := hNormal x
  have hc := Normal.ResidueCartier.BundleCycles.normalResidue_principal_regularUnit X x (Normal.PointResidue.BundleCycles.residueDivisorSupport_coheight X g h x) a
    (ha.map (X.presheaf.germ ⊤ x (by trivial)).hom) g h hg
  exact hc.trans (by rw [principalCartierPointCycle_globalUnit X a ha, smul_zero])

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Cartier.Unit.BundleCycles
