import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly
import Mathlib.Topology.Compactness.Compact

/-! # Finite Support Assembly -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles

noncomputable section

/-!
# Finite assembly of actual homology classes with compact support

The hypotheses in these generic lemmas concern the actual relative singular
homology of each compact piece. They prove finite-cover detection and gluing;
the geometric manifold instance is constructed separately.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : TopCat.{0})

/-- Evaluation of support restriction followed by local restriction. -/
theorem homologyWithSupportRestriction_toPoint_apply {K L : Set X}
    (hKL : K ⊆ L) (n : ℕ) (a : HomologyWithSupports.Cycles.singularHomologyWithSupport X L n)
    (x : X) (hx : x ∈ K) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n (CompactSupportAssembly.Cycles.homologyWithSupportRestriction X hKL n a) =
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x (hKL hx) n a :=
  ConcreteCategory.congr_hom (CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X hKL x hx n) a

/-- Zero detection at all points also detects equality of two classes. -/
theorem supportPointwise_ext (K : Set X) (n : ℕ)
    (hdet : ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K n,
      (∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = 0) → a = 0)
    (a b : HomologyWithSupports.Cycles.singularHomologyWithSupport X K n)
    (hab : ∀ x (hx : x ∈ K),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n b) : a = b := by
  apply sub_eq_zero.mp
  apply hdet
  intro x hx
  rw [map_sub, hab x hx, sub_self]

/-- Point restrictions detect a class on a binary union if they detect
both pieces and the next intersection group vanishes. -/
theorem supportUnion_eq_zero_of_pointwise (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (hInt : IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∩ L) (n + 1)))
    (hdetK : ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K n,
      (∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = 0) → a = 0)
    (hdetL : ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X L n,
      (∀ x (hx : x ∈ L), LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x hx n a = 0) → a = 0)
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∪ L) n)
    (ha : ∀ x (hx : x ∈ K ∪ L), LocalHomologyPresheaf.Cycles.localHomologyToPoint X (K ∪ L) x hx n a = 0) :
    a = 0 := by
  apply CompactSupportAssembly.Cycles.supportUnion_ext X K L hK hL n hInt a 0
  · rw [map_zero]
    apply hdetK
    intro x hx
    rw [homologyWithSupportRestriction_toPoint_apply]
    exact ha x (Or.inl hx)
  · rw [map_zero]
    apply hdetL
    intro x hx
    rw [homologyWithSupportRestriction_toPoint_apply]
    exact ha x (Or.inr hx)

/-- Classes having the same specified local values glue across a binary
closed cover when point restrictions detect classes on the overlap. -/
theorem supportUnion_glue_of_pointwise (K L : Set X)
    (hK : IsClosed K) (hL : IsClosed L) (n : ℕ)
    (hdetInt : ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∩ L) n,
      (∀ x (hx : x ∈ K ∩ L), LocalHomologyPresheaf.Cycles.localHomologyToPoint X (K ∩ L) x hx n a = 0) → a = 0)
    (u : ∀ x : X, LocalHomology.Cycles.localSingularHomology X x n)
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K n)
    (b : HomologyWithSupports.Cycles.singularHomologyWithSupport X L n)
    (ha : ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = u x)
    (hb : ∀ x (hx : x ∈ L), LocalHomologyPresheaf.Cycles.localHomologyToPoint X L x hx n b = u x) :
    ∃ c : HomologyWithSupports.Cycles.singularHomologyWithSupport X (K ∪ L) n,
      ∀ x (hx : x ∈ K ∪ L), LocalHomologyPresheaf.Cycles.localHomologyToPoint X (K ∪ L) x hx n c = u x := by
  have hab : CompactSupportAssembly.Cycles.homologyWithSupportRestriction X
      (Set.inter_subset_left : K ∩ L ⊆ K) n a =
      CompactSupportAssembly.Cycles.homologyWithSupportRestriction X (Set.inter_subset_right : K ∩ L ⊆ L) n b := by
    apply supportPointwise_ext X (K ∩ L) n hdetInt
    intro x hx
    rw [homologyWithSupportRestriction_toPoint_apply,
      homologyWithSupportRestriction_toPoint_apply, ha x hx.1, hb x hx.2]
  obtain ⟨c, hcK, hcL⟩ := CompactSupportAssembly.Cycles.supportUnion_glue X K L hK hL n a b hab
  refine ⟨c, ?_⟩
  intro x hx
  rcases hx with hx | hx
  · rw [← homologyWithSupportRestriction_toPoint_apply X
      (Set.subset_union_left : K ⊆ K ∪ L) n c x hx, hcK]
    exact ha x hx
  · rw [← homologyWithSupportRestriction_toPoint_apply X
      (Set.subset_union_right : L ⊆ K ∪ L) n c x hx, hcL]
    exact hb x hx

variable [T2Space X]

/-- Vanishing above a degree propagates to a finite compact union when
it holds for every compact subset of each individual member. -/
theorem finiteSupportUnion_isZero {ι : Type} (s : Finset ι) (C : ι → Set X) (d : ℕ)
    (hC : ∀ i ∈ s, IsCompact (C i))
    (hzero : ∀ i ∈ s, ∀ K : Set X, IsCompact K → K ⊆ C i →
      ∀ n : ℕ, d < n → IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X K n)) :
    ∀ n : ℕ, d < n → IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X (⋃ i ∈ s, C i) n) := by
  classical
  revert hC hzero
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ n _
      simpa only [Set.biUnion_empty_finset] using CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X n
  | @insert i s hi ih =>
      intro hC hzero n hn
      have hCi := hC i (Finset.mem_insert_self i s)
      have hCs : ∀ j ∈ s, IsCompact (C j) :=
        fun j hj => hC j (Finset.mem_insert_of_mem hj)
      have hU := s.isCompact_biUnion hCs
      have hzs : ∀ j ∈ s, ∀ K : Set X, IsCompact K → K ⊆ C j →
          ∀ m : ℕ, d < m → IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X K m) :=
        fun j hj => hzero j (Finset.mem_insert_of_mem hj)
      rw [Finset.set_biUnion_insert]
      apply CompactSupportAssembly.Cycles.supportUnion_isZero X (C i) (⋃ j ∈ s, C j) hCi.isClosed hU.isClosed n
      · exact hzero i (Finset.mem_insert_self i s) (C i) hCi (Set.Subset.refl _) n hn
      · exact ih hCs hzs n hn
      · exact hzero i (Finset.mem_insert_self i s) _ (hCi.inter hU)
          Set.inter_subset_left (n + 1) (lt_trans hn (Nat.lt_succ_self n))

/-- Top-degree point detection propagates to a finite compact cover. -/
theorem finiteSupportUnion_eq_zero_of_pointwise {ι : Type} (s : Finset ι)
    (C : ι → Set X) (d : ℕ)
    (hC : ∀ i ∈ s, IsCompact (C i))
    (hzero : ∀ i ∈ s, ∀ K : Set X, IsCompact K → K ⊆ C i →
      ∀ n : ℕ, d < n → IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X K n))
    (hdet : ∀ i ∈ s, ∀ K : Set X, IsCompact K → K ⊆ C i →
      ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K d,
        (∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx d a = 0) → a = 0) :
    ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X (⋃ i ∈ s, C i) d,
      (∀ x (hx : x ∈ ⋃ i ∈ s, C i),
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X (⋃ i ∈ s, C i) x hx d a = 0) → a = 0 := by
  classical
  revert hC hzero hdet
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _ a _
      have hz : IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X (⋃ i ∈ (∅ : Finset ι), C i) d) := by
        simpa only [Set.biUnion_empty_finset] using CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X d
      exact (ModuleCat.isZero_iff_subsingleton.mp hz).elim _ _
  | @insert i s hi ih =>
      intro hC hzero hdet
      have hCi := hC i (Finset.mem_insert_self i s)
      have hCs : ∀ j ∈ s, IsCompact (C j) :=
        fun j hj => hC j (Finset.mem_insert_of_mem hj)
      have hU := s.isCompact_biUnion hCs
      rw [Finset.set_biUnion_insert]
      exact supportUnion_eq_zero_of_pointwise X (C i) (⋃ j ∈ s, C j)
        hCi.isClosed hU.isClosed d
        (hzero i (Finset.mem_insert_self i s) _ (hCi.inter hU)
          Set.inter_subset_left (d + 1) (Nat.lt_succ_self d))
        (hdet i (Finset.mem_insert_self i s) (C i) hCi (Set.Subset.refl _))
        (ih hCs (fun j hj => hzero j (Finset.mem_insert_of_mem hj))
          (fun j hj => hdet j (Finset.mem_insert_of_mem hj)))

/-- Actual classes on finitely many compact supports glue when their local
values agree and point restrictions detect every compact overlap. -/
theorem finiteSupportUnion_glue {ι : Type} (s : Finset ι) (C : ι → Set X) (n : ℕ)
    (hC : ∀ i ∈ s, IsCompact (C i))
    (hdet : ∀ i ∈ s, ∀ K : Set X, IsCompact K → K ⊆ C i →
      ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K n,
        (∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n a = 0) → a = 0)
    (u : ∀ x : X, LocalHomology.Cycles.localSingularHomology X x n)
    (hclass : ∀ i ∈ s, ∃ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X (C i) n,
      ∀ x (hx : x ∈ C i), LocalHomologyPresheaf.Cycles.localHomologyToPoint X (C i) x hx n a = u x) :
    ∃ a : HomologyWithSupports.Cycles.singularHomologyWithSupport X (⋃ i ∈ s, C i) n,
      ∀ x (hx : x ∈ ⋃ i ∈ s, C i),
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X (⋃ i ∈ s, C i) x hx n a = u x := by
  classical
  revert hC hdet hclass
  induction s using Finset.induction_on with
  | empty =>
      intro _ _ _
      refine ⟨0, ?_⟩
      intro x hx
      simp only [Set.biUnion_empty_finset, Set.mem_empty_iff_false] at hx
  | @insert i s hi ih =>
      intro hC hdet hclass
      have hCi := hC i (Finset.mem_insert_self i s)
      have hCs : ∀ j ∈ s, IsCompact (C j) :=
        fun j hj => hC j (Finset.mem_insert_of_mem hj)
      have hU := s.isCompact_biUnion hCs
      obtain ⟨a, ha⟩ := hclass i (Finset.mem_insert_self i s)
      obtain ⟨b, hb⟩ := ih hCs (fun j hj => hdet j (Finset.mem_insert_of_mem hj))
        (fun j hj => hclass j (Finset.mem_insert_of_mem hj))
      rw [Finset.set_biUnion_insert]
      exact supportUnion_glue_of_pointwise X (C i) (⋃ j ∈ s, C j)
        hCi.isClosed hU.isClosed n
        (hdet i (Finset.mem_insert_self i s) _ (hCi.inter hU) Set.inter_subset_left)
        u a b ha hb

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles
