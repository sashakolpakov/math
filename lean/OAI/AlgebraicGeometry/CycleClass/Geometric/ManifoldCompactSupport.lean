import OAI.AlgebraicGeometry.CycleClass.Geometric.EuclideanCompactSupport
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactSupportCharts
import OAI.AlgebraicGeometry.CycleClass.Geometric.CompactChartCover
import OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupportAssembly

/-! # Manifold Compact Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ManifoldCompactSupport.Cycles

noncomputable section

/-!
# Compact-support homology on complex coordinate manifolds

Actual chart excision transports Euclidean compact-support vanishing and
point detection to every compact subset of a finite-dimensional complex
coordinate manifold. Finite compact chart refinements and the proved
Mayer--Vietoris assembly supply the passage from one chart to the manifold.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section OneChart

variable (p : ℕ) {X : TopCat.{0}} [T2Space X]
variable (e : OpenPartialHomeomorph X (Fin p → ℂ)) (K : Set X)
variable (hK : IsCompact K) (hKs : K ⊆ e.source)

include e hK hKs

/-- A compact support contained in a complex coordinate chart has no
relative homology above the real dimension. -/
theorem isZero_complexChart_compactSupport (n : ℕ) (hn : 2 * p < n) :
    IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport X K n) :=
  (EuclideanCompactSupport.Cycles.isZero_euclidean_compactSupport p (e '' K)
    (CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (Y := TopCat.of (Fin p → ℂ)) e K hK hKs)
    n hn).of_iso
      (CompactSupportCharts.Cycles.compactSupportChartHomologyIso (Y := TopCat.of (Fin p → ℂ)) e K hK hKs n)

/-- All point restrictions together detect the top group of a compact
support contained in one actual complex coordinate chart. -/
theorem complexChart_compactSupport_eq_zero_of_pointwise
    (a : HomologyWithSupports.Cycles.singularHomologyWithSupport X K (2 * p))
    (ha : ∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (2 * p) a = 0) : a = 0 := by
  let q := CompactSupportCharts.Cycles.compactSupportChartHomologyIso (Y := TopCat.of (Fin p → ℂ)) e K hK hKs (2 * p)
  have hz : q.hom a = 0 := by
    apply EuclideanCompactSupport.Cycles.euclidean_compactSupport_eq_zero_of_pointwise p (e '' K)
      (CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (Y := TopCat.of (Fin p → ℂ)) e K hK hKs)
    rintro y ⟨x, hx, rfl⟩
    have hs := ConcreteCategory.congr_hom
      (CompactSupportCharts.Cycles.compactSupportChartHomologyIso_toPoint (Y := TopCat.of (Fin p → ℂ))
        e K hK hKs (2 * p) x hx) a
    change LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (e '' K) (e x) _ (2 * p)
        (q.hom a) =
      (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (Y := TopCat.of (Fin p → ℂ))
        e x (hKs hx) (2 * p)).hom (LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (2 * p) a) at hs
    rw [hs, ha x hx, map_zero]
  apply q.toLinearEquiv.injective
  change q.hom a = q.hom 0
  rw [hz, map_zero]

/-- An actual coordinate compact-support class transported back through
the compact-support excision isomorphism of the chart. -/
def complexChartCompactSupportClass : HomologyWithSupports.Cycles.singularHomologyWithSupport X K (2 * p) :=
  (CompactSupportCharts.Cycles.compactSupportChartHomologyIso (Y := TopCat.of (Fin p → ℂ)) e K hK hKs (2 * p)).inv
    (ConvexSupportHomology.Cycles.complexCompactSupportClass p (e '' K)
      (CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (Y := TopCat.of (Fin p → ℂ)) e K hK hKs))

/-- At every supported point, the transported compact class is the
inverse local-chart image of the specified coordinate generator. -/
theorem complexChartCompactSupportClass_atPoint (x : X) (hx : x ∈ K) :
    LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (2 * p) (complexChartCompactSupportClass p e K hK hKs) =
      (LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (Y := TopCat.of (Fin p → ℂ))
        e x (hKs hx) (2 * p)).inv (ClosedBall.Cycles.complexCoordinatePointClass p (e x)) := by
  let q := CompactSupportCharts.Cycles.compactSupportChartHomologyIso (Y := TopCat.of (Fin p → ℂ)) e K hK hKs (2 * p)
  let l := LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (Y := TopCat.of (Fin p → ℂ))
    e x (hKs hx) (2 * p)
  let c := ConvexSupportHomology.Cycles.complexCompactSupportClass p (e '' K)
    (CompactSupportCharts.Cycles.compactSupportChart_image_isCompact (Y := TopCat.of (Fin p → ℂ)) e K hK hKs)
  have hs := ConcreteCategory.congr_hom
    (CompactSupportCharts.Cycles.compactSupportChartHomologyIso_toPoint (Y := TopCat.of (Fin p → ℂ))
      e K hK hKs (2 * p) x hx) (q.inv c)
  change LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of (Fin p → ℂ)) (e '' K) (e x) _ (2 * p)
      (q.hom (q.inv c)) = l.hom (LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (2 * p) (q.inv c)) at hs
  have hq : q.hom (q.inv c) = c := q.toLinearEquiv.apply_symm_apply c
  rw [hq, ConvexSupportHomology.Cycles.complexCompactSupportClass_atPoint] at hs
  apply l.toLinearEquiv.injective
  change l.hom (LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx (2 * p) (q.inv c)) =
    l.hom (l.inv (ClosedBall.Cycles.complexCoordinatePointClass p (e x)))
  rw [show l.hom (l.inv (ClosedBall.Cycles.complexCoordinatePointClass p (e x))) =
      ClosedBall.Cycles.complexCoordinatePointClass p (e x) from l.toLinearEquiv.apply_symm_apply _]
  exact hs.symm

end OneChart

variable (p : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
variable [ChartedSpace (Fin p → ℂ) M]

/-- Every compact support in a complex coordinate manifold has vanishing
relative singular homology above the real dimension. -/
theorem isZero_complexManifold_compactSupport (K : Set M) (hK : IsCompact K)
    (n : ℕ) (hn : 2 * p < n) :
    IsZero (HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K n) := by
  obtain ⟨s, r, C, hcover, hC⟩ := CompactChartCover.Cycles.exists_compact_chart_decomposition (Fin p → ℂ) hK
  have hsource (i : M) (hi : i ∈ s) : C i ⊆ (chartAt (Fin p → ℂ) i).source :=
    (hC i hi).2.2.2.1.trans (CompactChartCover.Cycles.chartClosedBallDomain_subset_source (Fin p → ℂ) i (r i))
  rw [hcover]
  apply FiniteSupportAssembly.Cycles.finiteSupportUnion_isZero (TopCat.of M) s C (2 * p)
    (fun i hi => (hC i hi).2.1) _ n hn
  intro i hi P hP hPC m hm
  exact isZero_complexChart_compactSupport p (X := TopCat.of M)
    (chartAt (Fin p → ℂ) i) P hP (hPC.trans (hsource i hi)) m hm

/-- Actual point restrictions detect top-degree classes on every compact
support of a complex coordinate manifold. -/
theorem complexManifold_compactSupport_eq_zero_of_pointwise (K : Set M) (hK : IsCompact K) :
    ∀ a : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * p),
      (∀ x (hx : x ∈ K), LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p) a = 0) → a = 0 := by
  obtain ⟨s, r, C, hcover, hC⟩ := CompactChartCover.Cycles.exists_compact_chart_decomposition (Fin p → ℂ) hK
  have hsource (i : M) (hi : i ∈ s) : C i ⊆ (chartAt (Fin p → ℂ) i).source :=
    (hC i hi).2.2.2.1.trans (CompactChartCover.Cycles.chartClosedBallDomain_subset_source (Fin p → ℂ) i (r i))
  rw [hcover]
  apply FiniteSupportAssembly.Cycles.finiteSupportUnion_eq_zero_of_pointwise (TopCat.of M) s C (2 * p)
    (fun i hi => (hC i hi).2.1)
  · intro i hi P hP hPC m hm
    exact isZero_complexChart_compactSupport p (X := TopCat.of M)
      (chartAt (Fin p → ℂ) i) P hP (hPC.trans (hsource i hi)) m hm
  · intro i hi P hP hPC a ha
    exact complexChart_compactSupport_eq_zero_of_pointwise p (X := TopCat.of M)
      (chartAt (Fin p → ℂ) i) P hP (hPC.trans (hsource i hi)) a ha

/-- Two top-degree compact-support classes agree as soon as their actual
restrictions at every supported point agree. -/
theorem complexManifold_compactSupport_point_ext (K : Set M) (hK : IsCompact K)
    {a b : HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * p)}
    (hab : ∀ x (hx : x ∈ K),
      LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p) a =
        LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p) b) : a = b :=
  FiniteSupportAssembly.Cycles.supportPointwise_ext (TopCat.of M) K (2 * p)
    (complexManifold_compactSupport_eq_zero_of_pointwise p K hK) a b hab

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ManifoldCompactSupport.Cycles
