import OAI.AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly
import Mathlib.Analysis.Convex.Basic

/-! # Finite Convex Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteConvexSupport.Cycles

noncomputable section

/-!
# Homology supported on finite unions of compact convex sets

The finite-family induction includes intersections with the last convex set.
Those intersections form a family on the same smaller index set. The
homological application uses the actual Mayer–Vietoris sequence of complement
pairs, and the orientation class is the restriction of a containing-ball class.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

private theorem finite_compact_convex_union_induction
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Set E → Prop) (hempty : P ∅)
    (hsingle : ∀ C : Set E, IsCompact C → Convex ℝ C → P C)
    (hunion : ∀ C D : Set E, IsCompact C → IsCompact D →
      P C → P D → P (C ∩ D) → P (C ∪ D))
    {ι : Type u} (s : Finset ι) :
    ∀ C : ι → Set E, (∀ i ∈ s, IsCompact (C i)) →
      (∀ i ∈ s, Convex ℝ (C i)) → P (⋃ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro C _ _
      simpa using hempty
  | @insert a s ha ih =>
      intro C hcompact hconvex
      have hCa : IsCompact (C a) := hcompact a (Finset.mem_insert_self a s)
      have hVa : Convex ℝ (C a) := hconvex a (Finset.mem_insert_self a s)
      have hCs : ∀ i ∈ s, IsCompact (C i) :=
        fun i hi => hcompact i (Finset.mem_insert_of_mem hi)
      have hVs : ∀ i ∈ s, Convex ℝ (C i) :=
        fun i hi => hconvex i (Finset.mem_insert_of_mem hi)
      have hInter : P (C a ∩ ⋃ i ∈ s, C i) := by
        simpa only [Set.inter_iUnion] using
          (ih (fun i => C a ∩ C i)
            (fun i hi => hCa.inter_right (hCs i hi).isClosed)
            (fun i hi => hVa.inter (hVs i hi)))
      have hUnion := hunion (C a) (⋃ i ∈ s, C i) hCa (s.isCompact_biUnion hCs)
        (hsingle (C a) hCa hVa) (ih C hCs hVs) hInter
      simpa only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left] using hUnion

private theorem finiteConvexSupport_main (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i)) :
    (∀ n : ℕ, 2 * p < n →
      IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) n)) ∧
    (∀ a b : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ))
        (⋃ i ∈ s, C i) (2 * p),
      (∀ x (hx : x ∈ ⋃ i ∈ s, C i),
        LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p) a =
          LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p) b) →
      a = b) := by
  classical
  let X := TopCat.of (Fin p → ℂ)
  let P : Set (Fin p → ℂ) → Prop := fun S =>
    (∀ n : ℕ, 2 * p < n → IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X S n)) ∧
    (∀ a b : HomologyWithSupports.Cycles.singularHomologyWithSupport X S (2 * p),
      (∀ x (hx : x ∈ S), LocalHomologyPresheaf.Cycles.localHomologyToPoint X S x hx (2 * p) a =
        LocalHomologyPresheaf.Cycles.localHomologyToPoint X S x hx (2 * p) b) → a = b)
  have hempty : P ∅ := by
    constructor
    · intro n _
      exact CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X n
    · intro a b _
      exact (ModuleCat.isZero_iff_subsingleton.mp
        (CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X (2 * p))).elim a b
  have hsingle : ∀ S : Set (Fin p → ℂ), IsCompact S → Convex ℝ S → P S := by
    intro S hS hconv
    by_cases hne : S.Nonempty
    · constructor
      · intro n hn
        exact ConvexSupportHomology.Cycles.complexConvexSupportHomology_isZero p S hS hconv hne n (ne_of_gt hn)
      · intro a b hab
        obtain ⟨x, hx⟩ := hne
        exact (ConvexSupportHomology.Cycles.convexSupportPointHomologyMap_bijective (Fin p → ℂ)
          S hS hconv x hx (2 * p)).1 (hab x hx)
    · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simpa only [hSempty] using hempty
  have hunion : ∀ S T : Set (Fin p → ℂ), IsCompact S → IsCompact T →
      P S → P T → P (S ∩ T) → P (S ∪ T) := by
    intro S T hS hT hPS hPT hPI
    constructor
    · intro n hn
      exact CompactSupportAssembly.Cycles.supportUnion_isZero X S T hS.isClosed hT.isClosed n
        (hPS.1 n hn) (hPT.1 n hn) (hPI.1 (n + 1) (by omega))
    · intro a b hab
      apply CompactSupportAssembly.Cycles.supportUnion_ext X S T hS.isClosed hT.isClosed (2 * p)
        (hPI.1 (2 * p + 1) (by omega)) a b
      · apply hPS.2
        intro x hx
        exact (ConcreteCategory.congr_hom
          (CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
            (Set.subset_union_left : S ⊆ S ∪ T) x hx (2 * p)) a).trans
          ((hab x (Or.inl hx)).trans (ConcreteCategory.congr_hom
            (CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
              (Set.subset_union_left : S ⊆ S ∪ T) x hx (2 * p)) b).symm)
      · apply hPT.2
        intro x hx
        exact (ConcreteCategory.congr_hom
          (CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
            (Set.subset_union_right : T ⊆ S ∪ T) x hx (2 * p)) a).trans
          ((hab x (Or.inr hx)).trans (ConcreteCategory.congr_hom
            (CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
              (Set.subset_union_right : T ⊆ S ∪ T) x hx (2 * p)) b).symm)
  exact finite_compact_convex_union_induction P hempty hsingle hunion s C hcompact hconvex

/-- The actual relative homology supported on a finite compact convex union
vanishes above the real dimension of complex coordinate space. -/
theorem finiteConvexSupportHomology_isZero (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i)) (n : ℕ) (hn : 2 * p < n) :
    IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) n) :=
  (finiteConvexSupport_main p s C hcompact hconvex).1 n hn

/-- Point restrictions jointly distinguish top-dimensional classes supported
on a finite union of compact convex subsets. -/
theorem finiteConvexSupport_point_ext (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i))
    {a b : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) (2 * p)}
    (h : ∀ x (hx : x ∈ ⋃ i ∈ s, C i),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p) a =
        LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p) b) :
    a = b :=
  (finiteConvexSupport_main p s C hcompact hconvex).2 a b h

/-- A top class on a finite compact convex union vanishes if all point
restrictions vanish. -/
theorem finiteConvexSupport_eq_zero (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i))
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) (2 * p))
    (h : ∀ x (hx : x ∈ ⋃ i ∈ s, C i),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p) a = 0) :
    a = 0 := by
  apply finiteConvexSupport_point_ext p s C hcompact hconvex
  intro x hx
  rw [map_zero]
  exact h x hx

/-- The specified orientation class on a finite compact union, obtained from
the genuine class of a containing coordinate ball. -/
def finiteConvexSupportClass (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i)) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) (2 * p) :=
  ConvexSupportHomology.Cycles.complexCompactSupportClass p (⋃ i ∈ s, C i) (s.isCompact_biUnion hcompact)

/-- The finite-union class has the prescribed local coordinate orientation
at every point of its support, including supports with several components. -/
theorem finiteConvexSupportClass_atPoint (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (x : Fin p → ℂ) (hx : x ∈ ⋃ i ∈ s, C i) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p)
        (finiteConvexSupportClass p s C hcompact) = ClosedBall.Cycles.complexCoordinatePointClass p x :=
  ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint p (⋃ i ∈ s, C i)
    (s.isCompact_biUnion hcompact) x hx

/-- Normalization at every point uniquely determines the orientation class. -/
theorem finiteConvexSupportClass_unique (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i))
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) (2 * p))
    (h : ∀ x (hx : x ∈ ⋃ i ∈ s, C i),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (⋃ i ∈ s, C i) x hx (2 * p) a =
        ClosedBall.Cycles.complexCoordinatePointClass p x) :
    a = finiteConvexSupportClass p s C hcompact := by
  apply finiteConvexSupport_point_ext p s C hcompact hconvex
  intro x hx
  rw [h x hx, finiteConvexSupportClass_atPoint]

/-- Restricting the class of any containing compact support gives the unique
normalized class on the finite compact convex union. -/
theorem finiteConvexSupportClass_restrict (p : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin p → ℂ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i))
    (L : Set (Fin p → ℂ)) (hL : IsCompact L) (hsub : (⋃ i ∈ s, C i) ⊆ L) :
    CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of (Fin p → ℂ)) hsub (2 * p)
        (ConvexSupportHomology.Cycles.complexCompactSupportClass p L hL) = finiteConvexSupportClass p s C hcompact := by
  apply finiteConvexSupportClass_unique p s C hcompact hconvex
  intro x hx
  exact (ConcreteCategory.congr_hom
    (CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint (TopCat.of (Fin p → ℂ)) hsub x hx (2 * p))
      (ConvexSupportHomology.Cycles.complexCompactSupportClass p L hL)).trans
    (ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint p L hL x (hsub hx))

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteConvexSupport.Cycles
