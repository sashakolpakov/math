import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.Topology.NoetherianSpace
import Mathlib.Data.Finsupp.Defs

/-! # Ord -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Ord.BundleCycles

noncomputable section

/-!
# LineBundleCycles: finiteness of principal divisors

On an integral Noetherian scheme, the order function of a rational function
has finite support. A nonzero rational function is a unit on a nonempty open;
only finitely many codimension-one points lie outside that open.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

universe u

theorem finite_codimension_one_complement
    (X : Scheme.{u}) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
    (U : X.Opens) [Nonempty U] :
    {x : X | coheight x = 1 ∧ x ∉ U}.Finite := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSU⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible U.isOpen.isClosed_compl
  let := hSf.to_subtype
  let C : S → IrreducibleCloseds X := fun s => ⟨s.1, hSi s.1 s.2, hSc s.1 s.2⟩
  let g : S → X := fun s => irreducibleSetEquivPoints (C s)
  apply (Set.finite_range g).subset
  intro x hx
  have hxc : x ∈ (U : Set X)ᶜ := hx.2
  rw [hSU] at hxc
  obtain ⟨s, hs, hxs⟩ := Set.mem_sUnion.mp hxc
  let s' : S := ⟨s, hs⟩
  let A : IrreducibleCloseds X := irreducibleSetEquivPoints.symm x
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hAC : A ≤ C s' := by
    change closure ({x} : Set X) ⊆ s
    exact (hSc s hs).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hxs)
  have hCT : C s' < T := by
    refine lt_of_le_of_ne (show C s' ≤ T from Set.subset_univ _) ?_
    intro heq
    obtain ⟨y⟩ := ‹Nonempty U›
    have hy : y.1 ∈ s := by
      change y.1 ∈ (C s' : Set X)
      rw [heq]
      trivial
    have hyc : y.1 ∈ (U : Set X)ᶜ := by
      rw [hSU]
      exact Set.mem_sUnion.mpr ⟨s, hs, hy⟩
    exact hyc y.2
  have hC1 : 1 ≤ coheight (C s') := by
    calc
      1 ≤ coheight T + 1 := le_add_self
      _ ≤ coheight (C s') := coheight_add_one_le hCT
  have hA1 : coheight A = 1 := by
    simpa only [A, coheight_orderIso] using hx.1
  have hEq : A = C s' := by
    apply le_antisymm hAC
    by_contra hCA
    have hlt : A < C s' := lt_of_le_not_ge hAC hCA
    have h2 : (2 : ℕ∞) ≤ coheight A := by
      calc
        2 = 1 + 1 := rfl
        _ ≤ coheight (C s') + 1 := add_le_add hC1 le_rfl
        _ ≤ coheight A := coheight_add_one_le hlt
    rw [hA1] at h2
    exact (by decide : ¬ (2 : ℕ∞) ≤ 1) h2
  refine ⟨s', ?_⟩
  change irreducibleSetEquivPoints (C s') = x
  rw [← hEq]
  exact irreducibleSetEquivPoints.apply_symm_apply x

/-- The actual local-length orders form a finite principal divisor. -/
theorem finite_support_ord (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) :
    (Function.support (X.ord f)).Finite := by
  classical
  by_cases hf : f = 0
  · subst f
    simp only [Scheme.ord_zero, Function.support_zero, Set.finite_empty]
  obtain ⟨U, _, a, hU, hfa, ha⟩ := exists_isUnit_germ_eq X f hf
  let := hU
  apply (finite_codimension_one_complement X U).subset
  intro x hx
  have hxne : X.ord f x ≠ 0 := hx
  constructor
  · by_contra hc
    exact hxne (Scheme.ord_eq_zero_of_coheight_neq_one hc f)
  · intro hxU
    apply hxne
    rw [← hfa]
    exact Scheme.ord_of_isUnit ha hxU

/-- The integral principal-divisor cycle, with no fallback on infinite support. -/
def principalDivisor (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) : X →₀ ℤ :=
  Finsupp.ofSupportFinite (X.ord f) (finite_support_ord X f)

@[simp]
theorem principalDivisor_apply (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f : X.functionField) (x : X) :
    principalDivisor X f x = X.ord f x := rfl

theorem principalDivisor_mul (X : Scheme.{u}) [IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X] (f g : X.functionField)
    (hf : f ≠ 0) (hg : g ≠ 0) :
    principalDivisor X (f * g) = principalDivisor X f + principalDivisor X g := by
  ext x
  exact Scheme.ord_mul hf hg

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Ord.BundleCycles
