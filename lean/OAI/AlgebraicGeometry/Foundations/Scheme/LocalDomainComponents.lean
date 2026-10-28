import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Local Domain Components -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents

noncomputable section

/-!
# Irreducible components of schemes with domain stalks

These are general scheme-theoretic lemmas with an explicit, local-domain
hypothesis. They do not assert that smoothness implies that hypothesis.
The key observation is that the generalizations of a point form an
irreducible set when its actual local ring is a domain.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.TopologicalSpace Set

universe u

variable {X : Scheme.{u}}

/-- The generalizations of a point form an irreducible set if the actual
stalk at that point is a domain. -/
theorem isIrreducible_generalizations_of_stalkDomain (x : X)
    [IsDomain (X.presheaf.stalk x)] : IsIrreducible {y : X | y ⤳ x} := by
  rw [← X.range_fromSpecStalk]
  simpa only [Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ (Spec (X.presheaf.stalk x))).image
      (X.fromSpecStalk x) (X.fromSpecStalk x).continuous.continuousOn

/-- Two irreducible components containing a point with domain local ring
are necessarily the same component. -/
theorem irreducibleComponents_eq_of_mem_of_stalkDomain
    (x : X) [IsDomain (X.presheaf.stalk x)]
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hW : W ∈ irreducibleComponents X) (hxZ : x ∈ Z) (hxW : x ∈ W) : Z = W := by
  let G : Set X := {y : X | y ⤳ x}
  have hG : IsIrreducible (closure G) :=
    (isIrreducible_generalizations_of_stalkDomain x).closure
  have hsub (T : Set X) (hT : T ∈ irreducibleComponents X) (hxT : x ∈ T) :
      T ⊆ closure G := by
    have hη := hT.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents T hT)
    have hηG : hT.1.genericPoint ∈ G := hη.specializes hxT
    rw [← hη]
    exact closure_mono (singleton_subset_iff.mpr hηG)
  have hZG : Z ⊆ closure G := hsub Z hZ hxZ
  have hWG : W ⊆ closure G := hsub W hW hxW
  exact subset_antisymm (hZG.trans (hW.2 hG hWG)) (hWG.trans (hZ.2 hG hZG))

/-- Distinct irreducible components are disjoint if all actual stalks are domains. -/
theorem irreducibleComponents_disjoint_of_stalkDomains
    (hlocal : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {Z W : Set X} (hZ : Z ∈ irreducibleComponents X)
    (hW : W ∈ irreducibleComponents X) (hne : Z ≠ W) : Disjoint Z W := by
  rw [Set.disjoint_left]
  intro x hxZ hxW
  let := hlocal x
  exact hne (irreducibleComponents_eq_of_mem_of_stalkDomain x hZ hW hxZ hxW)

/-- With finitely many components, domain stalks make each irreducible
component an open as well as a closed subset. -/
theorem isOpen_irreducibleComponent_of_stalkDomains
    (hlocal : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (hfinite : (irreducibleComponents X).Finite)
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) : IsOpen Z := by
  have heq : Z = (⋃₀ (irreducibleComponents X \ {Z}))ᶜ := by
    ext x
    constructor
    · intro hxZ hx
      rcases hx with ⟨W, ⟨hW, hWZ⟩, hxW⟩
      exact (Set.disjoint_left.mp
        (irreducibleComponents_disjoint_of_stalkDomains hlocal hW hZ
          (by simpa only [Set.mem_singleton_iff] using hWZ))) hxW hxZ
    · intro hx
      have hxc : x ∈ ⋃₀ irreducibleComponents X := by
        rw [sUnion_irreducibleComponents]
        trivial
      rcases hxc with ⟨W, hW, hxW⟩
      by_cases hWZ : W = Z
      · exact hWZ ▸ hxW
      · exact False.elim (hx ⟨W, ⟨hW, by simpa only [Set.mem_singleton_iff] using hWZ⟩, hxW⟩)
  rw [heq, isOpen_compl_iff, Set.sUnion_eq_biUnion]
  exact hfinite.sdiff.isClosed_biUnion fun W hW =>
    isClosed_of_mem_irreducibleComponents W hW.1

/-- A scheme whose actual local rings are domains is reduced. -/
theorem isReduced_of_stalkDomains
    (hlocal : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IsReduced X := by
  let (x : X) : IsDomain (X.presheaf.stalk x) := hlocal x
  exact isReduced_of_isReduced_stalk X

end

end OAI.AlgebraicGeometry.Foundations.Scheme.LocalDomainComponents
