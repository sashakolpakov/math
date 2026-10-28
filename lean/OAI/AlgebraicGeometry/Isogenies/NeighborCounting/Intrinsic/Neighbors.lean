import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.QuotientGraphs

/-! # Neighbors -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.Neighbors

noncomputable section

/-!
Reduced neighbors constructed from actual graph and product kernel maps.
Every index is an actual subspace of the generic active q-torsion. The
proved subspace equivalence selects its graph/product presentation; no
enumeration identity or reduced-target identity is a field of the data.

This bridge is for quotient sheaves of a supplied split integral block.
The input consists of actual schemes and morphisms. Identifying that split
block with every evaluated PEL lift and retaining polarization and marking
are separate from this quotient-sheaf theorem.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.SubspaceCounts.Construction

attribute [local instance] AbelianScheme.FrobeniusKernel.BaseChange.Construction.pulledBackGroup
attribute [local instance] Classical.propDecidable

/-- A literal scheme map presenting a subgroup action on the ambient scheme.
In the graph construction the domain is H_U; in the mixed construction it
is M x H_U. No specialization or counting assertion is stored here. -/
structure KernelPresentation {S : Scheme.{u}} (A : Over S) where
  carrier : Over S
  inclusion : carrier ⟶ A

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]
variable {S T : Scheme.{u}} {A M E : Over S} [GrpObj A] [GrpObj M]
variable (H : Submodule F V → Over S)
variable (b : M ⊗ E ⟶ A) (e : ∀ U, H U ⟶ E)
variable (χ : ∀ U : Submodule F V, (U →ₗ[F] F) → (H U ⟶ M))

def kernelOfLiftData : SubspaceCounts.Construction.LiftData F V → KernelPresentation A
  | ⟨U, Sum.inl L⟩ =>
      ⟨H U, QuotientGraphs.graphKernel b (e U) (χ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm L))⟩
  | ⟨U, Sum.inr _⟩ => ⟨M ⊗ H U, QuotientGraphs.mixedKernel b (e U)⟩

/-- The integral kernel associated to an actual generic active subspace. -/
def subspaceKernel (L : Submodule F (V × F)) : KernelPresentation A :=
  kernelOfLiftData H b e χ (SubspaceCounts.Construction.allSubspacesEquiv.symm L)

omit [GrpObj A] [GrpObj M] in
lemma subspaceKernel_equiv (d : SubspaceCounts.Construction.LiftData F V) :
    subspaceKernel H b e χ (SubspaceCounts.Construction.allSubspacesEquiv d) = kernelOfLiftData H b e χ d := by
  unfold subspaceKernel
  rw [Equiv.symm_apply_apply]

/-- The characteristic-zero target is the generic fiber of the integral
kernel quotient. The definition uses genuine sheaf base change. -/
def genericNeighborTarget {G : Scheme.{u}} (genericMap : G ⟶ S)
    (L : Submodule F (V × F)) : QuotientGraphs.QuotientTarget G :=
  QuotientGraphs.reducedQuotientTarget genericMap (subspaceKernel H b e χ L).inclusion

def reducedNeighborTarget (f : T ⟶ S)
    (L : Submodule F (V × F)) : QuotientGraphs.QuotientTarget T :=
  QuotientGraphs.reducedQuotientTarget f (subspaceKernel H b e χ L).inclusion

/-- Quotient target of the literal special etale or mixed kernel. -/
def specialKernelTarget (f : T ⟶ S) (U : Submodule F V) : Bool → QuotientGraphs.QuotientTarget T
  | false => QuotientGraphs.quotientTarget ((Over.pullback f).map (QuotientGraphs.graphKernel b (e U) 1))
  | true => QuotientGraphs.quotientTarget ((Over.pullback f).map (QuotientGraphs.mixedKernel b (e U)))

theorem reducedNeighborTarget_computed
    (f : T ⟶ S) (q : ℕ) (hq : q.Prime) (hT : (q : Γ(T, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq T hT)]
    [∀ U, Etale ((Over.pullback f).obj (H U)).hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hT ((Over.pullback f).obj M) = 1)
    (L : Submodule F (V × F)) :
    reducedNeighborTarget H b e χ f L =
      specialKernelTarget H b e f (L.map (LinearMap.fst F V F))
        (decide (SubspaceCounts.Construction.identityLine ≤ L)) := by
  classical
  obtain ⟨⟨U, L | L⟩, rfl⟩ := (SubspaceCounts.Construction.allSubspacesEquiv (F := F) (V := V)).surjective L
  · unfold reducedNeighborTarget
    rw [subspaceKernel_equiv]
    change QuotientGraphs.reducedQuotientTarget f
      (QuotientGraphs.graphKernel b (e U) (χ U ((SubspaceCounts.Construction.disjointLiftEquiv U).symm L))) = _
    change _ = specialKernelTarget H b e f (L.val.map (LinearMap.fst F V F))
      (decide (SubspaceCounts.Construction.identityLine ≤ L.val))
    rw [L.property.2,
      decide_eq_false (SubspaceCounts.Construction.identityLine_not_le_of_disjoint _ L.property.1)]
    exact QuotientGraphs.reduced_graph_quotient_eq f q hq hT hM b (e U) _
  · unfold reducedNeighborTarget
    rw [subspaceKernel_equiv]
    change QuotientGraphs.reducedQuotientTarget f (QuotientGraphs.mixedKernel b (e U)) = _
    change _ = specialKernelTarget H b e f (L.val.map (LinearMap.fst F V F))
      (decide (SubspaceCounts.Construction.identityLine ≤ L.val))
    rw [L.property.2, decide_eq_true L.property.1]
    exact QuotientGraphs.reducedQuotientTarget_eq f (QuotientGraphs.mixedKernel b (e U))

variable [Fintype F] [Fintype V]

local instance : Fintype (Submodule F V) := Fintype.ofFinite _
local instance : Fintype (Submodule F (V × F)) := Fintype.ofFinite _

/-- Enumerate all dimension-i generic kernels once, then reduce their
integral quotient targets. Repeated special targets remain in the multiset. -/
def reducedNeighbors (f : T ⟶ S) (i : ℕ) : Multiset (QuotientGraphs.QuotientTarget T) :=
  ∑ L : Submodule F (V × F),
    if Module.finrank F L = i then {reducedNeighborTarget H b e χ f L} else 0

/-- The geometric-to-counting bridge: it is proved kernel by kernel from
native quotient specialization and the Frobenius vanishing argument. -/
theorem reducedNeighbors_eq_labeledReduction
    (f : T ⟶ S) (q : ℕ) (hq : q.Prime) (hT : (q : Γ(T, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq T hT)]
    [∀ U, Etale ((Over.pullback f).obj (H U)).hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hT ((Over.pullback f).obj M) = 1)
    (i : ℕ) :
    reducedNeighbors H b e χ f i =
      SubspaceCounts.Construction.labeledReduction i (fun U flag => ({specialKernelTarget H b e f U flag} :
        Multiset (QuotientGraphs.QuotientTarget T))) := by
  classical
  unfold reducedNeighbors SubspaceCounts.Construction.labeledReduction
  apply Finset.sum_congr rfl
  intro L _
  rw [reducedNeighborTarget_computed H b e χ f q hq hT hM L]

/-- All three NeighborCounting multiplicities for native split-block quotient targets. -/
theorem native_quotient_reduction_multiplicities
    (f : T ⟶ S) (q : ℕ) (hq : q.Prime)
    (hcard : Nat.card F = q) (hV : Module.finrank F V = 2)
    (hT : (q : Γ(T, ⊤)) = 0)
    [IsIso (Picard.Homomorphisms.Frobenius.Construction.absoluteFrobenius q hq T hT)]
    [∀ U, Etale ((Over.pullback f).obj (H U)).hom]
    (hM : Picard.Homomorphisms.Frobenius.Construction.relativeFrobenius q hq hT ((Over.pullback f).obj M) = 1) :
    reducedNeighbors H b e χ f 1 =
      {specialKernelTarget H b e f ⊥ true} +
        q • (∑ U : Submodule F V,
          if Module.finrank F U = 1 then {specialKernelTarget H b e f U false} else 0) ∧
    reducedNeighbors H b e χ f 2 =
      (∑ U : Submodule F V,
        if Module.finrank F U = 1 then {specialKernelTarget H b e f U true} else 0) +
      q ^ 2 • ({specialKernelTarget H b e f ⊤ false} : Multiset (QuotientGraphs.QuotientTarget T)) ∧
    reducedNeighbors H b e χ f 3 = {specialKernelTarget H b e f ⊤ true} := by
  rw [reducedNeighbors_eq_labeledReduction H b e χ f q hq hT hM 1,
    reducedNeighbors_eq_labeledReduction H b e χ f q hq hT hM 2,
    reducedNeighbors_eq_labeledReduction H b e χ f q hq hT hM 3,
    SubspaceCounts.Construction.labeledReduction_one, SubspaceCounts.Construction.labeledReduction_two hV, SubspaceCounts.Construction.labeledReduction_three hV, hcard]
  exact ⟨rfl, rfl, rfl⟩

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.Neighbors
