import OAI.AlgebraicGeometry.Divisors.LineBundles.DimensionChow
import OAI.AlgebraicGeometry.Divisors.LineBundles.RegularDivisor

/-! # Cartier Cycle -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual principal Cartier intersection cycles

Restrict a global regular section to an integral support and take its
finite divisor, using the actual local-length orders. Its complete
support lies on the zero locus of that global section. The resulting
ambient cycle is a principal relation, including when the restricted
section vanishes identically and its order cycle is zero.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X]

theorem schemePrincipalPointDivisor_zero (W : IrreducibleCloseds X) :
    Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W 0 = 0 := by
  have h : Ord.BundleCycles.principalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) 0 = 0 := by
    ext x
    exact congrFun (Scheme.ord_zero (X := CycleClass.Geometric.GenericPoint.reducedSupportScheme W)) x
  unfold Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor
  rw [h, Finsupp.mapRange_zero, Finsupp.embDomain_zero]

theorem schemeGradedPrincipalDivisor_zero (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) (W : IrreducibleCloseds X) :
    Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W 0 = 0 := by
  ext x
  exact congrArg (fun z => z x.1) (schemePrincipalPointDivisor_zero W)

/-- The zero function also gives the zero relation; no nonzero-divisor premise is hidden. -/
theorem dimensionCycleToChowQ_principal_any (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (W : IrreducibleCloseds X) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    DimensionChow.BundleCycles.dimensionCycleToChowQ f d (Graded.GlobalSpecialization.BundleCycles.schemeGradedPrincipalDivisor f d W g) = 0 := by
  by_cases hg : g = 0
  · rw [hg, schemeGradedPrincipalDivisor_zero, map_zero]
  · exact DimensionChow.BundleCycles.dimensionCycleToChowQ_principal f d W hW g hg

/-- The actual rational function obtained by restricting the ambient regular section. -/
def supportRegularFunction (a : Γ(X, ⊤)) (W : IrreducibleCloseds X) :
    (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField :=
  RegularDivisor.BundleCycles.globalFunctionFieldElement (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop a)

/-- The complete point cycle of intersection with a principal Cartier equation. -/
def principalCartierPointCycle (a : Γ(X, ⊤)) (W : IrreducibleCloseds X) : X →₀ ℚ :=
  Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor W (supportRegularFunction a W)

/-- A nonzero intersection coefficient lies on the actual zero locus of the ambient section. -/
theorem principalCartierPointCycle_support (a : Γ(X, ⊤)) (W : IrreducibleCloseds X) :
    ((principalCartierPointCycle a W).support : Set X) ⊆ (X.basicOpen a : Set X)ᶜ := by
  intro x hx hxa
  have hxne : principalCartierPointCycle a W x ≠ 0 := Finsupp.mem_support_iff.mp hx
  have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    by_contra h
    exact hxne (Finsupp.embDomain_of_notMem_range _ _ _ h)
  obtain ⟨y, rfl⟩ := hr
  have hpre := Scheme.preimage_basicOpen_top (CycleClass.Geometric.GenericPoint.reducedSupportι W) a
  have hy : y ∈ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).basicOpen ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop a) :=
    (congrArg (fun U : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).Opens => y ∈ U) hpre).mp hxa
  have hz := RegularDivisor.BundleCycles.regularFunctionDivisor_eq_zero_of_isUnit_germ (CycleClass.Geometric.GenericPoint.reducedSupportScheme W)
    ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop a) y
    ((Scheme.mem_basicOpen (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) ((CycleClass.Geometric.GenericPoint.reducedSupportι W).appTop a) y (by trivial)).mp hy)
  exact hxne ((Graded.GlobalSpecialization.BundleCycles.schemePrincipalPointDivisor_at_support W (supportRegularFunction a W) y).trans
    ((congrArg (fun n : ℤ => (n : ℚ)) hz).trans Int.cast_zero))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Principal.CartierCycle.BundleCycles
