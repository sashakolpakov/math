import OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple
import Mathlib.Topology.Sets.Closeds
import Mathlib.Data.Fin.SuccPred
import Mathlib.Topology.LocallyClosed

/-! # Closed Support Filtration -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedSupportFiltration.Cycles

noncomputable section

/-!
# Vanishing along finite closed support filtrations

The layer between two closed subsets is considered in the actual open
complement of the smaller support. Its support cohomology is the existing
relative singular cohomology of that open space and the complement of the
layer. The genuine relative-cochain triple sequence supplies the induction
step. No geometric purity statement is assumed for arbitrary layers.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace
open OAI.AlgebraicGeometry.CycleClass.Geometric.RelativeCochainTriple.Cohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [Ring R]

/-- The layer between two closed supports, inside the actual open
complement of the smaller support. -/
def closedSupportLayer (X : TopCat.{0}) (F G : Closeds X) :
    Set (TopCat.of ((F : Set X)ᶜ : Set X)) :=
  {x | x.val ∈ (G : Set X)}

/-- The layer is closed in this open ambient space. -/
theorem closedSupportLayer_isClosed (X : TopCat.{0}) (F G : Closeds X) :
    IsClosed (closedSupportLayer X F G) :=
  G.isClosed.preimage continuous_subtype_val

/-- In the original space, the same layer is exactly the set difference. -/
theorem closedSupportLayer_image (X : TopCat.{0}) (F G : Closeds X) :
    Subtype.val '' closedSupportLayer X F G = (G : Set X) \ (F : Set X) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, hyG, rfl⟩
    exact ⟨hyG, hy⟩
  · rintro ⟨hxG, hxF⟩
    exact ⟨⟨x, hxF⟩, hxG, rfl⟩

/-- The same layer is locally closed in the original ambient space. -/
theorem closedSupportLayer_image_isLocallyClosed (X : TopCat.{0}) (F G : Closeds X) :
    IsLocallyClosed (Subtype.val '' closedSupportLayer X F G) := by
  rw [closedSupportLayer_image]
  exact G.isClosed.isLocallyClosed.inter F.isClosed.isOpen_compl.isLocallyClosed

/-- The complement of the layer is the literal subspace used by the
relative-cochain triple. -/
@[simp]
theorem closedSupportLayer_compl (X : TopCat.{0}) (F G : Closeds X) :
    (closedSupportLayer X F G)ᶜ =
      RelativeCochainTriple.Cohomology.relativeTripleSubspace X (F : Set X)ᶜ (G : Set X)ᶜ := rfl

/-- Empty support has zero genuine relative singular cohomology in every degree. -/
theorem cohomologyWithEmptySupport_isZero (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (n : ℕ) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (∅ : Set X)ᶜ n) := by
  let : IsIso (LocalHomology.Cycles.subspaceInclusion X Set.univ) := by
    change IsIso ((TopCat.isoOfHomeo (X := TopCat.of (Set.univ : Set X)) (Y := X)
      (Homeomorph.Set.univ X)).hom)
    infer_instance
  let : IsIso (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X Set.univ) := by
    dsimp only [AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction, AlgebraicTopology.Cohomology.Singular.Functor.singularPullback]
    let : IsIso (LocalHomology.Cycles.subspaceInclusion X Set.univ).op := inferInstance
    infer_instance
  have hz := isZero_kernel_of_mono (AlgebraicTopology.Cohomology.Singular.RelativeSequence.subspaceCochainRestriction M X Set.univ)
  have hh := (HomologicalComplex.homologyFunctor (ModuleCat.{0} R)
    (ComplexShape.up ℕ) n).map_isZero hz
  change IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X Set.univ n) at hh
  simpa only [Set.compl_empty] using hh

/-- Vanishing on the preceding closed support and on the next layer implies
vanishing on the enlarged support, by the actual triple exact sequence. -/
theorem closedSupportCohomology_isZero_step (M : ModuleCat.{0} R)
    (X : TopCat.{0}) (F G : Closeds X) (hFG : F ≤ G) (n : ℕ)
    (hF : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (F : Set X)ᶜ n))
    (hLayer : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M
      (TopCat.of ((F : Set X)ᶜ : Set X)) (closedSupportLayer X F G)ᶜ n)) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (G : Set X)ᶜ n) :=
  RelativeCochainTriple.Cohomology.relativeCohomologyTriple_isZero_middle M X (F : Set X)ᶜ (G : Set X)ᶜ
    (Set.compl_subset_compl.mpr hFG) n hF hLayer

/-- Finite induction along an actual increasing family of closed supports,
in one cohomological degree. -/
theorem closedSupportFiltration_isZero (M : ModuleCat.{0} R) (X : TopCat.{0})
    (N : ℕ) (F : Fin (N + 1) → Closeds X) (hF : Monotone F) (n : ℕ)
    (hfirst : IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (F 0 : Set X)ᶜ n))
    (hLayer : ∀ i : Fin N, IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M
      (TopCat.of ((F i.castSucc : Set X)ᶜ : Set X))
      (closedSupportLayer X (F i.castSucc) (F i.succ))ᶜ n)) :
    IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (F (Fin.last N) : Set X)ᶜ n) := by
  have h (i : Fin (N + 1)) :
      IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (F i : Set X)ᶜ n) := by
    induction i using Fin.induction with
    | zero => exact hfirst
    | succ i hi =>
      exact closedSupportCohomology_isZero_step M X (F i.castSucc) (F i.succ)
        (hF i.castSucc_le_succ) n hi (hLayer i)
  exact h (Fin.last N)

/-- The total support is exactly the union of the locally closed layers
of an increasing finite filtration starting at the empty set. -/
theorem closedSupportFiltration_union_layers (X : TopCat.{0})
    (N : ℕ) (F : Fin (N + 1) → Closeds X) (hF : Monotone F) (hfirst : F 0 = ⊥) :
    (⋃ i : Fin N, (F i.succ : Set X) \ (F i.castSucc : Set X)) =
      (F (Fin.last N) : Set X) := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion_subset fun i =>
      Set.sdiff_subset.trans (hF (Fin.le_last i.succ))
  · intro x hx
    by_contra hnot
    have hmem (i : Fin (N + 1)) : x ∉ (F i : Set X) := by
      induction i using Fin.induction with
      | zero => simp only [hfirst, Closeds.coe_bot, Set.mem_empty_iff_false, not_false_eq_true]
      | succ i hi =>
        intro hxnext
        exact hnot (Set.mem_iUnion.mpr ⟨i, hxnext, hi⟩)
    exact hmem (Fin.last N) hx

/-- If every locally closed layer in a finite closed-support filtration
starting at the empty set has support cohomology zero below `k`, then so
does the total support. The layer-vanishing premises concern the existing
relative singular cohomology groups, not a separate purity predicate. -/
theorem closedSupportFiltration_isZero_below (M : ModuleCat.{0} R) (X : TopCat.{0})
    (N : ℕ) (F : Fin (N + 1) → Closeds X) (hF : Monotone F) (hfirst : F 0 = ⊥)
    (k : ℕ)
    (hLayer : ∀ (i : Fin N) (n : ℕ), n < k →
      IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of ((F i.castSucc : Set X)ᶜ : Set X))
        (closedSupportLayer X (F i.castSucc) (F i.succ))ᶜ n)) :
    ∀ n < k, IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X (F (Fin.last N) : Set X)ᶜ n) := by
  intro n hn
  apply closedSupportFiltration_isZero M X N F hF n
  · simpa only [hfirst, Closeds.coe_bot] using cohomologyWithEmptySupport_isZero M X n
  · exact fun i => hLayer i n hn

/-- The vanishing conclusion stated for the explicit union of the actual
locally closed layers. -/
theorem closedSupportFiltration_union_isZero_below (M : ModuleCat.{0} R) (X : TopCat.{0})
    (N : ℕ) (F : Fin (N + 1) → Closeds X) (hF : Monotone F) (hfirst : F 0 = ⊥)
    (k : ℕ)
    (hLayer : ∀ (i : Fin N) (n : ℕ), n < k →
      IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M (TopCat.of ((F i.castSucc : Set X)ᶜ : Set X))
        (closedSupportLayer X (F i.castSucc) (F i.succ))ᶜ n)) :
    ∀ n < k, IsZero (AlgebraicTopology.Cohomology.Singular.RelativeSequence.relativeSingularCohomology M X
      (⋃ i : Fin N, (F i.succ : Set X) \ (F i.castSucc : Set X))ᶜ n) := by
  rw [closedSupportFiltration_union_layers X N F hF hfirst]
  exact closedSupportFiltration_isZero_below M X N F hF hfirst k hLayer

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ClosedSupportFiltration.Cycles
