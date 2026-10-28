import OAI.AlgebraicGeometry.DivisorClass.Chern.Open.Logarithms
import Mathlib.Topology.ShrinkingLemma

/-! # Log Refinement Open -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen

noncomputable section

/-!
# ChernClass: an open refinement with logarithms of every transition

A finite cover of a normal space is first shrunk. Near each point, transitions
between the finitely many relevant closed chart domains have local logarithms;
the other pairs can be avoided. Intersecting these neighborhoods gives a cover
whose pairwise overlaps admit logarithms of the original transitions.
-/

open _root_.TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Construction

variable {T I : Type*} [TopologicalSpace T]

/-- The continuous inclusion of one open set in another. -/
def openInclusionMap {A B : Opens T} (h : A ≤ B) : C(A, B) :=
  ⟨fun x => ⟨x.val, h x.property⟩,
    continuous_subtype_val.subtype_mk (fun x => h x.property)⟩

/-- A refinement carrying actual logarithms, with their exponential identities. -/
structure LogarithmicRefinement (U : I → Opens T)
    (g : ∀ i j, C((U i ⊓ U j : Opens T), ℂ)) where
  cover : T × I → Opens T
  subset : ∀ a, cover a ≤ U a.2
  covers : ∀ x, ∃ a, x ∈ cover a
  logarithm : ∀ a b, C((cover a ⊓ cover b : Opens T), ℂ)
  exp_logarithm : ∀ a b (x : (cover a ⊓ cover b : Opens T)),
    Complex.exp (logarithm a b x) =
      g a.2 b.2 ⟨x.val, subset a x.property.1, subset b x.property.2⟩

/-- Finite covers of normal spaces admit logarithmic refinements of any
family of nonvanishing continuous transition functions. -/
theorem nonempty_logarithmicRefinement [Finite I] [NormalSpace T]
    (U : I → Opens T) (hc : ∀ x, ∃ i, x ∈ U i)
    (g : ∀ i j, C((U i ⊓ U j : Opens T), ℂ)) (hg : ∀ i j x, g i j x ≠ 0) :
    Nonempty (LogarithmicRefinement U g) := by
  classical
  obtain ⟨V, hVc, hVo, hVU⟩ := exists_subset_iUnion_closure_subset
    (s := (Set.univ : Set T)) isClosed_univ (fun i => (U i).isOpen)
    (fun x _ => Set.toFinite {i | x ∈ U i}) (by
      intro x _
      obtain ⟨i, hi⟩ := hc x
      exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  let K : I → Set T := fun i => closure (V i)
  have hKU (i : I) : K i ⊆ U i := hVU i
  let H : T → I → I → Prop := fun p i j => p ∈ K i ∩ K j
  let localData (p : T) (i j : I) (h : H p i j) :
      Open.Logarithms.Construction.OpenLogarithm (U i ⊓ U j) (g i j) ⟨p, hKU i h.1, hKU j h.2⟩ :=
    Open.Logarithms.Construction.openLogarithm _ _ _ (hg i j _)
  let D (p : T) (i j : I) : Opens T :=
    if h : H p i j then (localData p i j h).domain else
      ⟨(K i ∩ K j)ᶜ, (isClosed_closure.inter isClosed_closure).isOpen_compl⟩
  have hD (p : T) (i j : I) : p ∈ D p i j := by
    dsimp [D]
    split_ifs with h
    · exact (localData p i j h).mem_domain
    · exact h
  let O : T → Opens T := fun p => ⨅ ij : I × I, D p ij.1 ij.2
  have hO (p : T) : p ∈ O p := by
    change p ∈ ((⨅ ij : I × I, D p ij.1 ij.2 : Opens T) : Set T)
    rw [Opens.coe_iInf]
    exact Set.mem_iInter.mpr (fun ij => hD p ij.1 ij.2)
  have hOD (p : T) (i j : I) : O p ≤ D p i j := iInf_le _ (i, j)
  let W : T × I → Opens T := fun a => O a.1 ⊓ ⟨V a.2, hVo a.2⟩
  have hWU (a : T × I) : W a ≤ U a.2 := by
    intro x hx
    exact hKU a.2 (subset_closure hx.2)
  have hWc (x : T) : ∃ a, x ∈ W a := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hVc (Set.mem_univ x))
    exact ⟨(x, i), hO x, hi⟩
  have hH (a b : T × I) (x : (W a ⊓ W b : Opens T)) : H a.1 a.2 b.2 := by
    by_contra h
    have hxD := hOD a.1 a.2 b.2 x.property.1.1
    have hxK : x.val ∈ K a.2 ∩ K b.2 :=
      ⟨subset_closure x.property.1.2, subset_closure x.property.2.2⟩
    change x.val ∈ D a.1 a.2 b.2 at hxD
    dsimp only [D] at hxD
    rw [dite_eq_right h] at hxD
    exact hxD hxK
  have hIn (a b : T × I) (h : H a.1 a.2 b.2) :
      W a ⊓ W b ≤ (localData a.1 a.2 b.2 h).domain := by
    intro x hx
    have hxD := hOD a.1 a.2 b.2 hx.1.1
    simpa only [D, dite_eq_left h] using hxD
  let logs (a b : T × I) : C((W a ⊓ W b : Opens T), ℂ) :=
    if h : H a.1 a.2 b.2 then
      (localData a.1 a.2 b.2 h).logarithm.comp
        (openInclusionMap (hIn a b h))
    else 0
  refine ⟨{
    cover := W
    subset := hWU
    covers := hWc
    logarithm := logs
    exp_logarithm := ?_ }⟩
  intro a b x
  have h := hH a b x
  dsimp only [logs]
  rw [dite_eq_left h]
  exact (localData a.1 a.2 b.2 h).exp_logarithm
    ⟨x.val, hIn a b h x.property⟩

/-- A logarithmic refinement of a chosen finite subcover. -/
structure CompactLogarithmicRefinement (U : I → Opens T)
    (g : ∀ i j, C((U i ⊓ U j : Opens T), ℂ)) where
  charts : Finset I
  refinement : LogarithmicRefinement (fun i : charts => U i.val)
    (fun i j => g i.val j.val)

/-- Compact normal spaces supply the finite subcover used in the construction. -/
theorem nonempty_compactLogarithmicRefinement [CompactSpace T] [NormalSpace T]
    (U : I → Opens T) (hc : ∀ x, ∃ i, x ∈ U i)
    (g : ∀ i j, C((U i ⊓ U j : Opens T), ℂ)) (hg : ∀ i j x, g i j x ≠ 0) :
    Nonempty (CompactLogarithmicRefinement U g) := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i => (U i : Set T)) (fun i => (U i).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr (hc x))
  have hsc : ∀ x, ∃ i : s, x ∈ U i.val := by
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hxi⟩
  obtain ⟨r⟩ := nonempty_logarithmicRefinement (fun i : s => U i.val) hsc
    (fun i j => g i.val j.val) (fun i j x => hg i.val j.val x)
  exact ⟨⟨s, r⟩⟩

end Construction

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.LogRefinementOpen
