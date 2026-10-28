import OAI.AlgebraicGeometry.CycleClass.Geometric.ManifoldCompactSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison

/-! # Complex Compact Fundamental -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles

noncomputable section

/-!
# Canonical integral compact-support classes on complex manifolds

For each compact subset of an actual complex manifold, finite chart assembly
constructs the unique relative singular homology class whose restriction at
every supported point is the chart-independent complex local generator.
Both the existence and uniqueness statements concern the actual integral
singular homology groups. No orientation class is assumed as input.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (p : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin p → ℂ) M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- On a compact support contained in an atlas chart, the transported
coordinate class has the canonical complex value at every supported point. -/
theorem complexChartCompactSupportClass_canonical
    (e : OpenPartialHomeomorph M (Fin p → ℂ)) (he : e ∈ atlas (Fin p → ℂ) M)
    (K : Set M) (hK : IsCompact K) (hKs : K ⊆ e.source) (x : M) (hx : x ∈ K) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p)
        (ManifoldCompactSupport.Cycles.complexChartCompactSupportClass p (X := TopCat.of M) e K hK hKs) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x := by
  rw [ManifoldCompactSupport.Cycles.complexChartCompactSupportClass_atPoint]
  let l := LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
    (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) e x (hKs hx) (2 * p)
  apply l.toLinearEquiv.injective
  change l.hom (l.inv (ClosedBall.Cycles.complexCoordinatePointClass p (e x))) =
    l.hom (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x)
  rw [show l.hom (l.inv (ClosedBall.Cycles.complexCoordinatePointClass p (e x))) =
      ClosedBall.Cycles.complexCoordinatePointClass p (e x) from l.toLinearEquiv.apply_symm_apply _]
  exact (ComplexCoordinateComparison.Cycles.complexCanonicalLocalClass_chart e he x (hKs hx)).symm

/-- A canonical complex local generator extends to an actual relative
homology class on every compact support, by finite chart gluing. -/
theorem exists_complexCompactFundamentalClass (K : Set M) (hK : IsCompact K) :
    ∃ a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * p),
      ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p) a =
        ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x := by
  obtain ⟨s, r, C, hcover, hC⟩ := CompactChartCover.Cycles.exists_compact_chart_decomposition (Fin p → ℂ) hK
  have hsource (i : M) (hi : i ∈ s) : C i ⊆ (chartAt (Fin p → ℂ) i).source :=
    (hC i hi).2.2.2.1.trans (CompactChartCover.Cycles.chartClosedBallDomain_subset_source (Fin p → ℂ) i (r i))
  rw [hcover]
  apply FiniteSupportAssembly.Cycles.finiteSupportUnion_glue (TopCat.of M) s C (2 * p)
    (fun i hi => (hC i hi).2.1)
    (fun _ _ P hP _ => ManifoldCompactSupport.Cycles.complexManifold_compactSupport_eq_zero_of_pointwise p P hP)
    (fun x => ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x)
  intro i hi
  refine ⟨ManifoldCompactSupport.Cycles.complexChartCompactSupportClass p (X := TopCat.of M)
    (chartAt (Fin p → ℂ) i) (C i) (hC i hi).2.1 (hsource i hi), ?_⟩
  intro x hx
  exact complexChartCompactSupportClass_canonical p (chartAt (Fin p → ℂ) i)
    (chart_mem_atlas (Fin p → ℂ) i) (C i) (hC i hi).2.1 (hsource i hi) x hx

/-- The unique integral fundamental class relative to the complement of
a compact support in a complex manifold. -/
def complexCompactFundamentalClass (K : Set M) (hK : IsCompact K) :
    HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * p) :=
  (exists_complexCompactFundamentalClass p K hK).choose

/-- The compact-support fundamental class has the actual complex local
generator as its restriction at every point of the support. -/
theorem complexCompactFundamentalClass_atPoint (K : Set M) (hK : IsCompact K)
    (x : M) (hx : x ∈ K) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p)
        (complexCompactFundamentalClass p K hK) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x :=
  (exists_complexCompactFundamentalClass p K hK).choose_spec x hx

/-- The prescribed complex local values uniquely determine the class. -/
theorem complexCompactFundamentalClass_unique (K : Set M) (hK : IsCompact K)
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * p))
    (ha : ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p) a =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) :
    a = complexCompactFundamentalClass p K hK := by
  apply ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext p K hK
  intro x hx
  rw [ha x hx, complexCompactFundamentalClass_atPoint]

/-- Existence and uniqueness use the actual integral relative group. -/
theorem existsUnique_complexCompactFundamentalClass (K : Set M) (hK : IsCompact K) :
    ∃! a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * p),
      ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p) a =
        ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x :=
  ⟨complexCompactFundamentalClass p K hK,
    complexCompactFundamentalClass_atPoint p K hK,
    complexCompactFundamentalClass_unique p K hK⟩

/-- The canonical classes form a compatible family under every inclusion
of compact support sets. -/
theorem complexCompactFundamentalClass_restriction (K L : Set M)
    (hK : IsCompact K) (hL : IsCompact L) (hKL : K ⊆ L) :
    CompactSupportAssembly.Cycles.homologyWithSupportRestriction (TopCat.of M) hKL (2 * p)
        (complexCompactFundamentalClass p L hL) =
      complexCompactFundamentalClass p K hK := by
  apply complexCompactFundamentalClass_unique p K hK
  intro x hx
  rw [FiniteSupportAssembly.Cycles.homologyWithSupportRestriction_toPoint_apply, complexCompactFundamentalClass_atPoint]

/-- A nonempty compact support has a nonzero normalized class. -/
theorem complexCompactFundamentalClass_ne_zero (K : Set M) (hK : IsCompact K)
    (hne : K.Nonempty) : complexCompactFundamentalClass p K hK ≠ 0 := by
  intro hz
  obtain ⟨x, hx⟩ := hne
  have h := complexCompactFundamentalClass_atPoint p K hK x hx
  rw [hz, map_zero] at h
  exact ComplexChartOrientation.Cycles.complexCanonicalLocalClass_ne_zero x h.symm

/-- The canonical empty-support class is zero in the zero relative group. -/
theorem complexCompactFundamentalClass_empty :
    complexCompactFundamentalClass p (∅ : Set M) isCompact_empty = 0 :=
  (ModuleCat.isZero_iff_subsingleton.mp
    (CompactSupportAssembly.Cycles.homologyWithSupport_empty_isZero (TopCat.of M) (2 * p))).elim _ _

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCompactFundamental.Cycles
