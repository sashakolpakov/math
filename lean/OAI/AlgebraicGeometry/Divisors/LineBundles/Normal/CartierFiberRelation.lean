import OAI.AlgebraicGeometry.Divisors.LineBundles.Global.NormalReciprocity
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedPrincipal
import OAI.AlgebraicGeometry.Divisors.LineBundles.Proper.ResidueBoundary
import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierSelfIntersection

/-! # Cartier Fiber Relation -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.CartierFiberRelation.BundleCycles

noncomputable section

/-!
# LineBundleCycles: principal Cartier intersection kills a rational divisor on a normal support

Away from the zero fiber, the actual residue divisor equals the
order-weighted Cartier term. On the fiber, the Cartier term is zero
and the residue divisor is a principal relation on that fiber.
The complete reciprocity sum therefore gives zero in the fiber Chow group.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open scoped Classical

variable {X Z : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (a : Γ(X, ⊤))
    (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ)

omit [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Z] in
include hzero in
theorem pointClosure_subset_zeroFiber (x : X) (hx : x ∉ X.basicOpen a) :
    (irreducibleSetEquivPoints.symm x : Set X) ⊆ Set.range j :=
  j.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
    (Set.singleton_subset_iff.mpr ((congrArg (fun S : Set X => x ∈ S) hzero).mpr hx))

variable [IsIntegral X] (hNormal : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x))
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]

include hNormal hzero

theorem normalPrincipalCartier_fiber_class_zero (ha : a ≠ 0) (d : ℕ)
    (hX : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f = d + 2) (g : X.functionFieldˣ) :
    Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d
      (Principal.CartierFiber.BundleCycles.principalCartierPointMap a (RationalDivisorRestriction.BundleCycles.rationalPrincipalPointDivisor X (g : X.functionField))) = 0 := by
  let ga := Units.mk0 (RegularDivisor.BundleCycles.globalFunctionFieldElement X a) (RegularDivisor.BundleCycles.globalFunctionFieldElement_ne_zero X a ha)
  let ρ := Point.CycleChow.BundleCycles.closedPointCycleToChowQ j f d
  let S := PointResidue.BundleCycles.residueDivisorSupport X ga g
  have hb := congrArg ρ (Global.NormalReciprocity.BundleCycles.normalResidueBoundaryCycle_zero X hNormal f ga g)
  unfold PointResidue.BundleCycles.normalResidueBoundaryCycle at hb
  rw [map_sum, map_zero] at hb
  rw [Proper.ResidueBoundary.BundleCycles.principalCartierPointMap_divisor_sum X a (g : X.functionField) S Finset.subset_union_right,
    map_sum]
  refine (Finset.sum_congr rfl ?_).trans hb
  intro x _
  let := hNormal x
  have hx := PointResidue.BundleCycles.residueDivisorSupport_coheight X ga g x
  rw [map_smul]
  by_cases hxa : (x : X) ∈ X.basicOpen a
  · have hu := (Scheme.mem_basicOpen X a x (by trivial)).mp hxa
    have he := congrArg ρ (ResidueCartier.BundleCycles.normalResidue_principal_regularUnit_rat X x hx a hu ga g rfl)
    rw [map_smul] at he
    exact he.symm
  · have hs := pointClosure_subset_zeroFiber j a hzero x hxa
    have hz : Principal.CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm (x : X)) = 0 := by
      unfold Principal.CartierCycle.BundleCycles.principalCartierPointCycle
      rw [Principal.CartierSelfIntersection.BundleCycles.supportRegularFunction_eq_zero a _ (hs.trans hzero.le), Principal.CartierCycle.BundleCycles.schemePrincipalPointDivisor_zero]
    rw [hz, map_zero, smul_zero]
    exact (Closed.SupportedPrincipal.BundleCycles.closedPointCycleToChowQ_supportedPrincipal j f d (irreducibleSetEquivPoints.symm (x : X))
      (PointResidue.BundleCycles.normalResidueSupport_dimension X f d hX ga g x) hs
      (PointResidue.BundleCycles.normalResidueFunctionOnSupport X hNormal ga g x)).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Normal.CartierFiberRelation.BundleCycles
