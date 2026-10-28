import OAI.ArithmeticGeometry.Descent.CMVariety.SmoothBaseNeighborhood
import OAI.ArithmeticGeometry.Descent.CMVariety.FiberChartProjection
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.Baire.Lemmas

/-! # Countable Neighborhood Isolation -/

namespace OAI.ArithmeticGeometry.Descent.CMVariety.CountableNeighborhoodIsolation.Abelian

noncomputable section

/-!
A countable neighborhood in a smooth complex scheme forces analytic
isolation. A positive-dimensional complex chart has no countable open
neighborhood, by the Baire theorem and absence of isolated points.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry Set
open scoped Classical _root_.Topology

theorem countable_open_empty_of_perfect_baire
    {X : Type} [TopologicalSpace X] [T1Space X] [PerfectSpace X] [BaireSpace X]
    {U : Set X} (hU : IsOpen U) (hcount : U.Countable) : U = ∅ := by
  have hsmall (x : X) : IsMeagre ({x} : Set X) := by
    apply IsNowhereDense.isMeagre
    rw [IsNowhereDense, isClosed_singleton.closure_eq, interior_singleton]
  have hmeagre : IsMeagre U := by
    simpa only [Set.biUnion_of_singleton] using isMeagre_biUnion hcount (fun x _ => hsmall x)
  by_contra hne
  exact not_isMeagre_of_isOpen hU (Set.nonempty_iff_ne_empty.mpr hne) hmeagre

theorem isolated_of_countable_neighborhood_complex_chart
    {X Index : Type} [TopologicalSpace X] [Fintype Index]
    (e : OpenPartialHomeomorph X (Index → ℂ)) (x : X) (hx : x ∈ e.source)
    {U : Set X} (hU : U ∈ 𝓝 x) (hcount : U.Countable) : IsOpen ({x} : Set X) := by
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hU
  have himage : IsOpen (e '' (W ∩ e.source)) :=
    e.isOpen_image_of_subset_source (hW.inter e.open_source) Set.inter_subset_right
  have hcimage : (e '' (W ∩ e.source)).Countable :=
    (hcount.mono (Set.inter_subset_left.trans hWU)).image e
  have hzero : Fintype.card Index = 0 := by
    by_contra hn
    let : Nonempty Index := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hn)
    let : PerfectSpace (Index → ℂ) := perfectSpace_of_module ℂ _
    have he := countable_open_empty_of_perfect_baire himage hcimage
    have hm : e x ∈ e '' (W ∩ e.source) := ⟨x, ⟨hxW, hx⟩, rfl⟩
    rw [he] at hm
    exact hm
  let : IsEmpty Index := Fintype.card_eq_zero_iff.mp hzero
  have heq : e.source = {x} := by
    ext y
    constructor
    · intro hy
      exact e.injOn hy hx (Subsingleton.elim _ _)
    · rintro rfl
      exact hx
  rw [← heq]
  exact e.open_source

theorem native_isolated_of_countable_neighborhood
    (S : Over AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth S.hom] (s : AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)
    {U : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)} (hU : U ∈ 𝓝 s) (hcount : U.Countable) :
    IsOpen ({s} : Set (AlgebraicGeometry.ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints S)) := by
  obtain ⟨R, b, hb, y, P, hy⟩ := SmoothBaseNeighborhood.Abelian.RelativeCharts.exists_smooth_affine_base_neighborhood S s
  let : IsOpenImmersion b.left := hb
  obtain ⟨e, hey, _, _⟩ := AlgebraicGeometry.ComplexPoints.Analytic.SmoothAffineCharts.exists_standardSmooth_point_chart P.presentation y
  let a := AnalyticSchemeFamilies.Abelian.RelativeCharts.nativeAffineChart R b e
  have hs : s ∈ a.source := ⟨y, hey, hy⟩
  exact isolated_of_countable_neighborhood_complex_chart a s hs hU hcount

end

end OAI.ArithmeticGeometry.Descent.CMVariety.CountableNeighborhoodIsolation.Abelian
