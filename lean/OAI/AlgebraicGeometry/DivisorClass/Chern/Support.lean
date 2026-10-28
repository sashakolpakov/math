import OAI.AlgebraicGeometry.DivisorClass.Chern.Rational.Coordinates
import Mathlib.Topology.NoetherianSpace
import Mathlib.Data.Finsupp.Defs
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport

/-! # Support -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-!
# ChernClass: finite support of the rational section's divisor

The finite-complement argument follows the local LineBundleCycles divisor-support proof:
in an integral Noetherian scheme, only finitely many codimension-one points
lie outside any nonempty open. The rational section is a generator on its
reference chart, so its nonzero orders are supported on this finite set.
-/

open _root_.AlgebraicGeometry _root_.TopologicalSpace _root_.Order

namespace Support.Construction

/-- A nonempty open misses only finitely many codimension-one points. -/
theorem finite_codimension_one_complement
    (X : Scheme) [IsIntegral X] [AlgebraicGeometry.IsNoetherian X]
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
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
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
  have hA1 : coheight A = 1 := by simpa only [A, coheight_orderIso] using hx.1
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

end Support.Construction

variable {X : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation} (L : Line.Bundles.AlgebraicLineBundle X)
variable [IsIntegral X.carrier]

/-- The actual local-length multiplicities of the rational section have finite support. -/
theorem Line.Bundles.AlgebraicLineBundle.finite_support_rationalSectionOrder : (Function.support L.rationalSectionOrder).Finite := by
  let : Nonempty L.rationalReferenceOpen :=
    ⟨⟨genericPoint X.carrier, L.mem_trivializingOpen _⟩⟩
  apply (Support.Construction.finite_codimension_one_complement X.carrier L.rationalReferenceOpen).subset
  intro x hx
  constructor
  · by_contra hc
    exact hx (L.rationalSectionOrder_eq_zero_of_coheight_ne_one x hc)
  · intro hU
    exact hx (L.rationalSectionOrder_zero_on_reference x hU)

/-- The divisor of the chosen actual rational section, indexed by scheme points. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionPointDivisor : X.carrier →₀ ℤ :=
  Finsupp.ofSupportFinite L.rationalSectionOrder L.finite_support_rationalSectionOrder

@[simp]
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionPointDivisor_apply (x : X.carrier) :
    L.rationalSectionPointDivisor x = L.rationalSectionOrder x := rfl

/-- The same divisor in mathlib's genuine locally finite algebraic-cycle type. -/
def Line.Bundles.AlgebraicLineBundle.rationalSectionAlgebraicDivisor : AlgebraicCycle X.carrier ℤ :=
  CycleClass.Geometric.FiniteSupport.Cycles.finsuppToAlgebraicCycle L.rationalSectionPointDivisor

@[simp]
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionAlgebraicDivisor_apply (x : X.carrier) :
    L.rationalSectionAlgebraicDivisor x = L.rationalSectionOrder x := rfl

/-- Every point with nonzero multiplicity has order-theoretic codimension one. -/
theorem Line.Bundles.AlgebraicLineBundle.rationalSectionAlgebraicDivisor_coheight_one (x : X.carrier)
    (hx : L.rationalSectionAlgebraicDivisor x ≠ 0) : coheight x = 1 := by
  by_contra h
  exact hx (L.rationalSectionOrder_eq_zero_of_coheight_ne_one x h)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
