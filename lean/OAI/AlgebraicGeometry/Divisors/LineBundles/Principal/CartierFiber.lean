import OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportedCycleLift
import OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.ChowPushforward

/-! # Cartier Fiber -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: principal intersection cycles on the actual closed zero fiber

The finite divisor of the restricted equation has the required dimension
and lies on its closed zero fiber. Transport to that fiber retains every
coefficient. Linear extension constructs the intersection operation on
cycles. Its descent with respect to relations on the source remains a
separate assertion; no such compatibility enters this construction.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Z : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (j : Z ⟶ X) [IsClosedImmersion j] (a : Γ(X, ⊤)) (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

def principalCartierGradedCycle (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1)) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ :=
  Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d (irreducibleSetEquivPoints.symm x.1)
    (CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x.1))

def principalCartierFiberCycle (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1)) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ :=
  Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift j f d (principalCartierGradedCycle a f d x)

variable (hzero : Set.range j = (X.basicOpen a : Set X)ᶜ) [LocallyOfFiniteType f]

include hzero in
/-- The zero-fiber cycle pushes to the full graded divisor of the restricted equation. -/
theorem principalCartierFiberCycle_push (d : ℕ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1)) :
    Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d (principalCartierFiberCycle j a f d x) =
      principalCartierGradedCycle a f d x := by
  apply Closed.SupportedCycleLift.BundleCycles.closedSupportedCycleLift_push
  have hp := Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d (irreducibleSetEquivPoints.symm x.1) x.2
    (CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x.1))
  intro y hy
  have hy' : y ∈ (CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x.1)).support :=
    (congrArg (fun z => y ∈ z.support) hp).mp hy
  exact (congrArg (fun s : Set X => y ∈ s) hzero).mpr
    (CartierCycle.BundleCycles.principalCartierPointCycle_support a (irreducibleSetEquivPoints.symm x.1) hy')

/-- Linear extension of the actual principal intersection cycles onto the zero fiber. -/
def principalCartierFiberCycleMap (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (j ≫ f) d →₀ ℚ) :=
  Finsupp.linearCombination ℚ (principalCartierFiberCycle j a f d)

/-- The same intersection cycles in the ambient scheme. -/
def principalCartierAmbientCycleMap (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.linearCombination ℚ (principalCartierGradedCycle a f d)

include hzero in
theorem principalCartierFiberCycleMap_push (d : ℕ) :
    (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d).comp (principalCartierFiberCycleMap j a f d) =
      principalCartierAmbientCycleMap a f d := by
  have hb : (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d) ∘ principalCartierFiberCycle j a f d =
      principalCartierGradedCycle a f d := funext (principalCartierFiberCycle_push j a f hzero d)
  exact (Finsupp.linearCombination_linear_comp ℚ (Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d)).symm.trans
    (congrArg (Finsupp.linearCombination ℚ) hb)

omit [LocallyOfFiniteType f] in
/-- Each ambient intersection cycle is the actual principal relation, including the zero-function case. -/
theorem principalCartierAmbientCycleMap_chow_zero (d : ℕ) :
    (DimensionChow.BundleCycles.dimensionCycleToChowQ f d).comp (principalCartierAmbientCycleMap a f d) = 0 := by
  apply Finsupp.lhom_ext
  intro x q
  change DimensionChow.BundleCycles.dimensionCycleToChowQ f d
    (Finsupp.linearCombination ℚ (principalCartierGradedCycle a f d) (Finsupp.single x q)) = 0
  rw [Finsupp.linearCombination_single, map_smul]
  have h := CartierCycle.BundleCycles.dimensionCycleToChowQ_principal_any f d (irreducibleSetEquivPoints.symm x.1) x.2
    (CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x.1))
  exact (congrArg (fun v => q • v) h).trans (smul_zero q)

variable [AlgebraicGeometry.IsNoetherian Z]

/-- The actual fiber Chow class of an intersection cycle, before source-relation descent. -/
def principalCartierFiberClassMap (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) →ₗ[ℚ] DimensionChow.BundleCycles.DimensionChowQ (j ≫ f) d :=
  (DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d).comp (principalCartierFiberCycleMap j a f d)

include hzero in
/-- Pushing the constructed fiber class into the ambient Chow group gives zero. -/
theorem principalCartierFiberClassMap_push_zero (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d (principalCartierFiberClassMap j a f d z) = 0 := by
  change Closed.ChowPushforward.BundleCycles.closedChowPushforward j f d
    (DimensionChow.BundleCycles.dimensionCycleToChowQ (j ≫ f) d (principalCartierFiberCycleMap j a f d z)) = 0
  rw [Closed.ChowPushforward.BundleCycles.closedChowPushforward_cycle]
  have hp := LinearMap.congr_fun (principalCartierFiberCycleMap_push j a f hzero d) z
  change Closed.CyclePushforward.BundleCycles.closedDimensionCyclePushforward j f d (principalCartierFiberCycleMap j a f d z) =
    principalCartierAmbientCycleMap a f d z at hp
  rw [hp]
  exact LinearMap.congr_fun (principalCartierAmbientCycleMap_chow_zero a f d) z

end

/-!
# LineBundleCycles: the ungraded principal Cartier operation and the existing graded construction

Linearly extend the actual principal divisor of the restricted equation
over the point-indexed cycle group. On every correct dimension grade,
this recovers the complete existing ambient Cartier intersection map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X] (a : Γ(X, ⊤))

def principalCartierPointMap : (X →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.linearCombination ℚ (fun x => CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x))

theorem principalCartierPointMap_single (x : X) (q : ℚ) :
    principalCartierPointMap a (Finsupp.single x q) =
      q • CartierCycle.BundleCycles.principalCartierPointCycle a (irreducibleSetEquivPoints.symm x) := by
  rw [principalCartierPointMap, Finsupp.linearCombination_single]

theorem principalCartierPointMap_graded (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f] (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f (d + 1) →₀ ℚ) :
    principalCartierPointMap a (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + 1) z) =
      Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (principalCartierAmbientCycleMap a f d z) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z w hz hw => simp only [map_add, hz, hw]
  | single x q =>
    have hi : Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f (d + 1) (Finsupp.single x q) = Finsupp.single x.val q :=
      Finsupp.mapDomain_single
    rw [hi, principalCartierPointMap_single,
      principalCartierAmbientCycleMap, Finsupp.linearCombination_single, map_smul]
    exact congrArg (fun c => q • c)
      (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor_push f d (irreducibleSetEquivPoints.symm x.1) x.2
        (CartierCycle.BundleCycles.supportRegularFunction a (irreducibleSetEquivPoints.symm x.1))).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierFiber.BundleCycles
