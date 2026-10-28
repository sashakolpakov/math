import OAI.AlgebraicTopology.Duality.RealLocalHomology
import OAI.AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactChartCover
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly

/-! # Real Support -/

namespace OAI.AlgebraicTopology.FundamentalClass.RealSupport.IntegrationGeometry

noncomputable section

/-! Integration: real-manifold compact-support detection, generalizing the checked
complex-coordinate finite-convex and finite-chart arguments. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem realCoordinateLocalHomology_isZero (d i : ℕ) (hi : i ≠ d)
    (x : Fin d → ℝ) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin d → ℝ)) x i) := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).symm.toHomeomorph
  have h := (Duality.RealLocalHomology.Constructions.PoincarePairing.realEuclideanLocalHomology_isZero d i hi).of_iso
    (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of (Fin d → ℝ))
      (Y := TopCat.of (EuclideanSpace ℝ (Fin d))) e 0 i)
  exact h.of_iso (AlgebraicGeometry.CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso (Fin d → ℝ) x i)

theorem realConvexSupportHomology_isZero (d : ℕ) (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty)
    (i : ℕ) (hi : i ≠ d) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) K i) := by
  obtain ⟨x, hx⟩ := hne
  exact (realCoordinateLocalHomology_isZero d i hi x).of_iso
    (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.convexSupportPointHomologyIso (Fin d → ℝ) K hK hconv x hx i)

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

private theorem finiteConvexSupport_main (d : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin d → ℝ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i)) :
    (∀ n : ℕ, d < n →
      IsZero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) n)) ∧
    (∀ a b : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ))
        (⋃ i ∈ s, C i) (d),
      (∀ x (hx : x ∈ ⋃ i ∈ s, C i),
        AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) x hx (d) a =
          AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) x hx (d) b) →
      a = b) := by
  classical
  let X := TopCat.of (Fin d → ℝ)
  let P : Set (Fin d → ℝ) → Prop := fun S =>
    (∀ n : ℕ, d < n → IsZero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X S n)) ∧
    (∀ a b : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X S (d),
      (∀ x (hx : x ∈ S), AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X S x hx (d) a =
        AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X S x hx (d) b) → a = b)
  have hempty : P ∅ := by
    constructor
    · intro n _
      exact AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X n
    · intro a b _
      exact (ModuleCat.isZero_iff_subsingleton.mp
        (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero X (d))).elim a b
  have hsingle : ∀ S : Set (Fin d → ℝ), IsCompact S → Convex ℝ S → P S := by
    intro S hS hconv
    by_cases hne : S.Nonempty
    · constructor
      · intro n hn
        exact realConvexSupportHomology_isZero d S hS hconv hne n (ne_of_gt hn)
      · intro a b hab
        obtain ⟨x, hx⟩ := hne
        exact (AlgebraicGeometry.CycleClass.Geometric.ConvexSupportHomology.Cycles.convexSupportPointHomologyMap_bijective (Fin d → ℝ)
          S hS hconv x hx (d)).1 (hab x hx)
    · have hSempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      simpa only [hSempty] using hempty
  have hunion : ∀ S T : Set (Fin d → ℝ), IsCompact S → IsCompact T →
      P S → P T → P (S ∩ T) → P (S ∪ T) := by
    intro S T hS hT hPS hPT hPI
    constructor
    · intro n hn
      exact AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.supportUnion_isZero X S T hS.isClosed hT.isClosed n
        (hPS.1 n hn) (hPT.1 n hn) (hPI.1 (n + 1) (by omega))
    · intro a b hab
      apply AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.supportUnion_ext X S T hS.isClosed hT.isClosed (d)
        (hPI.1 (d + 1) (by omega)) a b
      · apply hPS.2
        intro x hx
        exact (ConcreteCategory.congr_hom
          (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
            (Set.subset_union_left : S ⊆ S ∪ T) x hx (d)) a).trans
          ((hab x (Or.inl hx)).trans (ConcreteCategory.congr_hom
            (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
              (Set.subset_union_left : S ⊆ S ∪ T) x hx (d)) b).symm)
      · apply hPT.2
        intro x hx
        exact (ConcreteCategory.congr_hom
          (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
            (Set.subset_union_right : T ⊆ S ∪ T) x hx (d)) a).trans
          ((hab x (Or.inr hx)).trans (ConcreteCategory.congr_hom
            (AlgebraicGeometry.CycleClass.Geometric.CompactSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint X
              (Set.subset_union_right : T ⊆ S ∪ T) x hx (d)) b).symm)
  exact finite_compact_convex_union_induction P hempty hsingle hunion s C hcompact hconvex

/-- The actual relative homology supported on a finite compact convex union
vanishes above the real dimension of real coordinate space. -/
theorem finiteConvexSupportHomology_isZero (d : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin d → ℝ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i)) (n : ℕ) (hn : d < n) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) n) :=
  (finiteConvexSupport_main d s C hcompact hconvex).1 n hn

/-- Point restrictions jointly distinguish top-dimensional classes supported
on a finite union of compact convex subsets. -/
theorem finiteConvexSupport_point_ext (d : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin d → ℝ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i))
    {a b : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) (d)}
    (h : ∀ x (hx : x ∈ ⋃ i ∈ s, C i),
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) x hx (d) a =
        AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) x hx (d) b) :
    a = b :=
  (finiteConvexSupport_main d s C hcompact hconvex).2 a b h

/-- A top class on a finite compact convex union vanishes if all point
restrictions vanish. -/
theorem finiteConvexSupport_eq_zero (d : ℕ) {ι : Type u} (s : Finset ι)
    (C : ι → Set (Fin d → ℝ)) (hcompact : ∀ i ∈ s, IsCompact (C i))
    (hconvex : ∀ i ∈ s, Convex ℝ (C i))
    (a : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) (d))
    (h : ∀ x (hx : x ∈ ⋃ i ∈ s, C i),
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (⋃ i ∈ s, C i) x hx (d) a = 0) :
    a = 0 := by
  apply finiteConvexSupport_point_ext d s C hcompact hconvex
  intro x hx
  rw [map_zero]
  exact h x hx

/-- Relative homology supported on an arbitrary compact subset of real
coordinate space vanishes above its real dimension. -/
theorem isZero_euclidean_compactSupport (d : ℕ) (K : Set (Fin d → ℝ))
    (hK : IsCompact K) (i : ℕ) (hi : d < i) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin d → ℝ)) Kᶜ i) := by
  apply AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles.isZero_relativeHomology_of_cofinal_supports (TopCat.of (Fin d → ℝ)) K i
  intro U hKU
  obtain ⟨s, radius, hs, hKint, hLU, _⟩ :=
    AlgebraicGeometry.CycleClass.Geometric.CompactConvexNeighborhood.Cycles.exists_finite_closedBall_neighborhood hK U.isOpen hKU
  refine ⟨_, hKint.trans interior_subset, hLU, ?_⟩
  exact finiteConvexSupportHomology_isZero d s
    (fun x => Metric.closedBall x (radius x))
    (fun x hx => (hs x hx).2.2.1)
    (fun x hx => (hs x hx).2.2.2.1) i hi

/-- A top-dimensional class supported on an arbitrary compact subset of
real coordinate space vanishes when every point restriction vanishes. -/
theorem euclidean_compactSupport_eq_zero_of_pointwise
    (d : ℕ) (K : Set (Fin d → ℝ)) (hK : IsCompact K)
    (a : AlgebraicGeometry.CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomology (TopCat.of (Fin d → ℝ)) Kᶜ (d))
    (ha : ∀ (x : Fin d → ℝ) (hx : x ∈ K),
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) K x hx (d) a = 0) : a = 0 := by
  refine AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport.Cycles.relativeHomology_eq_zero_of_cofinal_point_detection
    (TopCat.of (Fin d → ℝ)) K (d) ?_ a ha
  intro U hKU
  obtain ⟨s, radius, hs, hKint, hLU, _⟩ :=
    AlgebraicGeometry.CycleClass.Geometric.CompactConvexNeighborhood.Cycles.exists_finite_closedBall_neighborhood hK U.isOpen hKU
  refine ⟨_, hKint.trans interior_subset, hLU, ?_⟩
  intro b hb
  exact finiteConvexSupport_eq_zero d s
    (fun x => Metric.closedBall x (radius x))
    (fun x hx => (hs x hx).2.2.1)
    (fun x hx => (hs x hx).2.2.2.1) b hb

section OneChart

variable (d : ℕ) {X : TopCat.{0}} [T2Space X]
variable (e : OpenPartialHomeomorph X (Fin d → ℝ)) (K : Set X)
variable (hK : IsCompact K) (hKs : K ⊆ e.source)

include e hK hKs

/-- A compact support contained in a real coordinate chart has no
relative homology above the real dimension. -/
theorem isZero_realChart_compactSupport (n : ℕ) (hn : d < n) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X K n) :=
  (isZero_euclidean_compactSupport d (e '' K)
    (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (Y := TopCat.of (Fin d → ℝ)) e K hK hKs)
    n hn).of_iso
      (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso (Y := TopCat.of (Fin d → ℝ)) e K hK hKs n)

/-- All point restrictions together detect the top group of a compact
support contained in one actual real coordinate chart. -/
theorem realChart_compactSupport_eq_zero_of_pointwise
    (a : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X K (d))
    (ha : ∀ x (hx : x ∈ K), AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (d) a = 0) : a = 0 := by
  let q := AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso (Y := TopCat.of (Fin d → ℝ)) e K hK hKs (d)
  have hz : q.hom a = 0 := by
    apply euclidean_compactSupport_eq_zero_of_pointwise d (e '' K)
      (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (Y := TopCat.of (Fin d → ℝ)) e K hK hKs)
    rintro y ⟨x, hx, rfl⟩
    have hs := ConcreteCategory.congr_hom
      (AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts.Cycles.compactSupportChartHomologyIso_toPoint (Y := TopCat.of (Fin d → ℝ))
        e K hK hKs (d) x hx) a
    change AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin d → ℝ)) (e '' K) (e x) _ (d)
        (q.hom a) =
      (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (Y := TopCat.of (Fin d → ℝ))
        e x (hKs hx) (d)).hom (AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (d) a) at hs
    rw [hs, ha x hx, map_zero]
  apply q.toLinearEquiv.injective
  change q.hom a = q.hom 0
  rw [hz, map_zero]

end OneChart

variable (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin d → ℝ) M]

/-- Every compact support in a real coordinate manifold has vanishing
relative singular homology above the real dimension. -/
theorem isZero_realManifold_compactSupport (K : Set M) (hK : IsCompact K)
    (n : ℕ) (hn : d < n) :
    IsZero (AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K n) := by
  obtain ⟨s, r, C, hcover, hC⟩ := AlgebraicGeometry.CycleClass.Geometric.CompactChartCover.Cycles.exists_compact_chart_decomposition (Fin d → ℝ) hK
  have hsource (i : M) (hi : i ∈ s) : C i ⊆ (chartAt (Fin d → ℝ) i).source :=
    (hC i hi).2.2.2.1.trans (AlgebraicGeometry.CycleClass.Geometric.CompactChartCover.Cycles.chartClosedBallDomain_subset_source (Fin d → ℝ) i (r i))
  rw [hcover]
  apply AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.finiteSupportUnion_isZero (TopCat.of M) s C (d)
    (fun i hi => (hC i hi).2.1) _ n hn
  intro i hi P hP hPC m hm
  exact isZero_realChart_compactSupport d (X := TopCat.of M)
    (chartAt (Fin d → ℝ) i) P hP (hPC.trans (hsource i hi)) m hm

/-- Actual point restrictions detect top-degree classes on every compact
support of a real coordinate manifold. -/
theorem realManifold_compactSupport_eq_zero_of_pointwise (K : Set M) (hK : IsCompact K) :
    ∀ a : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (d),
      (∀ x (hx : x ∈ K), AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (d) a = 0) → a = 0 := by
  obtain ⟨s, r, C, hcover, hC⟩ := AlgebraicGeometry.CycleClass.Geometric.CompactChartCover.Cycles.exists_compact_chart_decomposition (Fin d → ℝ) hK
  have hsource (i : M) (hi : i ∈ s) : C i ⊆ (chartAt (Fin d → ℝ) i).source :=
    (hC i hi).2.2.2.1.trans (AlgebraicGeometry.CycleClass.Geometric.CompactChartCover.Cycles.chartClosedBallDomain_subset_source (Fin d → ℝ) i (r i))
  rw [hcover]
  apply AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.finiteSupportUnion_eq_zero_of_pointwise (TopCat.of M) s C (d)
    (fun i hi => (hC i hi).2.1)
  · intro i hi P hP hPC m hm
    exact isZero_realChart_compactSupport d (X := TopCat.of M)
      (chartAt (Fin d → ℝ) i) P hP (hPC.trans (hsource i hi)) m hm
  · intro i hi P hP hPC a ha
    exact realChart_compactSupport_eq_zero_of_pointwise d (X := TopCat.of M)
      (chartAt (Fin d → ℝ) i) P hP (hPC.trans (hsource i hi)) a ha

/-- Two top-degree compact-support classes agree as soon as their actual
restrictions at every supported point agree. -/
theorem realManifold_compactSupport_point_ext (K : Set M) (hK : IsCompact K)
    {a b : AlgebraicGeometry.CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (d)}
    (hab : ∀ x (hx : x ∈ K),
      AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (d) a =
        AlgebraicGeometry.CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (d) b) : a = b :=
  AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly.Cycles.supportPointwise_ext (TopCat.of M) K (d)
    (realManifold_compactSupport_eq_zero_of_pointwise d K hK) a b hab

end

end OAI.AlgebraicTopology.FundamentalClass.RealSupport.IntegrationGeometry
