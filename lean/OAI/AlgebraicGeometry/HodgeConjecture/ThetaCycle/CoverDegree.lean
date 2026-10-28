import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverLocal
import OAI.AlgebraicGeometry.Cycles.Functoriality.FiniteFundamental
import OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality

/-! # Cover Degree -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverDegree.CM

noncomputable section

/-! Integral covering degree from actual finite fibers and holomorphic sheets.
This carries out ThetaCoverDegree's finite-fiber argument with the canonical complex local
classes directly; no integration identity or global degree law is an input. -/

open _root_.CategoryTheory _root_.TopologicalSpace
open OAI.AlgebraicTopology.Cohomology.Singular.EvaluationNaturality OAI.AlgebraicGeometry.Cycles.Functoriality.FiniteFundamental.Construction
open scoped _root_.Manifold

/-- A top homology class supported on finitely many points is the sum of
its restrictions, inserted through neighborhoods isolating those points. -/
theorem complex_finite_support_decomposition
    (d : ℕ) {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (Fin d → ℂ) M]
    (K : Set M) [Fintype K] (U : K → Opens M)
    (hxU : ∀ x : K, x.val ∈ U x)
    (hUK : ∀ (x : K) (z : U x), z.val ∈ K → z.val = x.val)
    (a : CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of M) K (2 * d)) :
    (∑ x : K, Cycles.Functoriality.FiniteFundamental.Construction.finiteSupportLocalInsertion K (U x) ⟨x.val, hxU x⟩
      (fun z hz => Subtype.ext (hUK x z hz)) (2 * d)
      ((CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U x) x.val (hxU x)
        (U x).isOpen (2 * d)).inv
        (CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x.val x.property (2 * d) a))) = a := by
  classical
  apply CycleClass.Geometric.ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext d K (Set.toFinite K).isCompact
  intro z hzK
  rw [map_sum, Finset.sum_eq_single (⟨z, hzK⟩ : K)]
  · have h := ConcreteCategory.congr_hom
      (Cycles.Functoriality.FiniteFundamental.Construction.finiteSupportLocalInsertion_to_self K (U ⟨z, hzK⟩)
        ⟨z, hxU ⟨z, hzK⟩⟩ hzK
        (fun w hw => Subtype.ext (hUK ⟨z, hzK⟩ w hw)) (2 * d))
      ((CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U ⟨z, hzK⟩) z
        (hxU ⟨z, hzK⟩) (U ⟨z, hzK⟩).isOpen (2 * d)).inv
        (CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K z hzK (2 * d) a))
    exact h.trans (Iso.inv_hom_id_apply
      (CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of M) (U ⟨z, hzK⟩) z
        (hxU ⟨z, hzK⟩) (U ⟨z, hzK⟩).isOpen (2 * d)) _)
  · intro x _ hx
    have hzx : z ≠ x.val := fun h => hx (Subtype.ext h.symm)
    exact ConcreteCategory.congr_hom
      (Cycles.Functoriality.FiniteFundamental.Construction.finiteSupportLocalInsertion_to_other K (U x) ⟨x.val, hxU x⟩ _
        z hzK hzx (2 * d)) _
  · simp

/-- The map of relative homology from a fiber to its image point. -/
def fiber_push {X Y : TopCat.{0}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport X (f ⁻¹' {y}) n ⟶ CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology Y y n :=
  CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap f (A := (f ⁻¹' {y})ᶜ) (B := {y}ᶜ) (fun _ hx => hx) n

/-- Pushing an inserted local class through one sheet is exactly the
local homology isomorphism of that sheet. -/
theorem sheet_push_insert
    {X Y : TopCat.{0}} [T1Space X] [T1Space Y]
    (f : X ⟶ Y) (e : OpenPartialHomeomorph X Y)
    (he : Set.EqOn f e e.source) (x : X) (hx : x ∈ e.source)
    (hUK : ∀ z : e.source, z.val ∈ f ⁻¹' {e x} → z = ⟨x, hx⟩)
    (n : ℕ) (a : CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology X x n) :
    fiber_push f (e x) n
      (Cycles.Functoriality.FiniteFundamental.Construction.finiteSupportLocalInsertion (f ⁻¹' {e x}) ⟨e.source, e.open_source⟩
        ⟨x, hx⟩ hUK n
        ((CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).inv a)) =
      (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x hx n).hom a := by
  let i : TopCat.of e.source ⟶ X := CycleClass.Geometric.LocalHomology.Cycles.subspaceInclusion X e.source
  have hi : Set.MapsTo i ({(⟨x, hx⟩ : e.source)} : Set e.source)ᶜ
      (f ⁻¹' {e x})ᶜ := fun z hz hzK => hz (hUK z hzK)
  have hf : Set.MapsTo f (f ⁻¹' {e x})ᶜ ({e x} : Set Y)ᶜ := fun _ hz => hz
  have hfe : i ≫ f = CycleClass.Geometric.LocalChartMaps.Cycles.openPartialSourceMap e := by
    ext z
    exact he z.property
  have hmaps : Cycles.Functoriality.FiniteFundamental.Construction.finiteSupportLocalInsertion (f ⁻¹' {e x})
      ⟨e.source, e.open_source⟩ ⟨x, hx⟩ hUK n ≫ fiber_push f (e x) n =
      CycleClass.Geometric.LocalChartMaps.Cycles.injectiveLocalHomologyMap (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialSourceMap e)
        (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialSourceMap_injective e) (⟨x, hx⟩ : e.source) n :=
    (CycleClass.Geometric.LocalHomology.Cycles.relativeSingularHomologyMap_comp i f hi hf n).trans
      (CycleClass.Geometric.LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hfe _ _ n)
  rw [← CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomology_source e x hx n] at hmaps
  have h := ConcreteCategory.congr_hom hmaps
    ((CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n).inv a)
  exact h.trans (congrArg (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso e x hx n).hom
    (Iso.inv_hom_id_apply (CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso X e.source x hx e.open_source n) a))

theorem absolute_support_at_point
    (X : TopCat.{0}) (K : Set X) (x : X) (hx : x ∈ K) (n : ℕ)
    (a : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains X).homology n) :
    CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint X K x hx n
      (HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X Kᶜ) n a) =
    HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection X ({x}ᶜ : Set X)) n a := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (CycleClass.Geometric.LocalHomologyPresheaf.Cycles.relativeComplementChainToPoint_projection X K x hx)
  rw [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h a

theorem complex_absolute_top_ext
    (d : ℕ) {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ChartedSpace (Fin d → ℂ) X]
    (a b : (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChains (TopCat.of X)).homology (2 * d))
    (hab : ∀ x : X,
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of X) ({x}ᶜ : Set X)) (2 * d) a =
      HomologicalComplex.homologyMap
        (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of X) ({x}ᶜ : Set X)) (2 * d) b) : a = b := by
  let q := CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso (TopCat.of X) (2 * d)
  apply q.toLinearEquiv.symm.injective
  apply CycleClass.Geometric.ManifoldCompactSupport.Cycles.complexManifold_compactSupport_point_ext d Set.univ isCompact_univ
  intro x hx
  exact (ConcreteCategory.congr_hom
    (CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso_inv_toPoint (TopCat.of X) (2 * d) x) a).trans
      ((hab x).trans (ConcreteCategory.congr_hom
        (CycleClass.Geometric.CompactManifoldFundamental.Cycles.wholeSpaceSupportHomologyIso_inv_toPoint (TopCat.of X) (2 * d) x) b).symm)

variable {d : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] [T2Space Y]
  [ChartedSpace (Fin d → ℂ) X] [ChartedSpace (Fin d → ℂ) Y]
  [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 X] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 Y]

omit [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 X] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 Y] in
theorem sheet_push_generator
    (f : TopCat.of Y ⟶ TopCat.of X) (e : OpenPartialHomeomorph Y X)
    (he : Set.EqOn f e e.source) (z : Y) (hz : z ∈ e.source)
    (x : X) (hex : e z = x)
    (hUK : ∀ w : e.source, w.val ∈ f ⁻¹' {x} → w = ⟨z, hz⟩)
    (ho : (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
      (X := TopCat.of Y) (Y := TopCat.of X) e z hz (2 * d)).hom
        (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) z) = CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (e z)) :
    fiber_push f x (2 * d)
      (Cycles.Functoriality.FiniteFundamental.Construction.finiteSupportLocalInsertion (f ⁻¹' {x}) ⟨e.source, e.open_source⟩
        ⟨z, hz⟩ hUK (2 * d)
        ((CycleClass.Geometric.LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of Y) e.source z hz e.open_source (2 * d)).inv
          (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) z))) = CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x := by
  subst x
  exact (sheet_push_insert f e he z hz hUK (2 * d) (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) z)).trans ho

omit [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 X] [IsManifold 𝓘(ℂ, Fin d → ℂ) 1 Y] in
/-- All local contributions from a finite fiber add with positive sign. -/
theorem complex_fiber_push_degree
    (f : TopCat.of Y ⟶ TopCat.of X)
    (horientation : ∀ y : Y,
      ∃ (e : OpenPartialHomeomorph Y X) (hy : y ∈ e.source),
        Set.EqOn e f e.source ∧
        (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso
          (X := TopCat.of Y) (Y := TopCat.of X)
          e y hy (2 * d)).hom (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y) = CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) (e y))
    (x : X) (hfinite : (f ⁻¹' {x}).Finite)
    (a : CycleClass.Geometric.HomologyWithSupports.Cycles.singularHomologyWithSupport (TopCat.of Y) (f ⁻¹' {x}) (2 * d))
    (ha : ∀ y (hy : y ∈ f ⁻¹' {x}),
      CycleClass.Geometric.LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of Y) (f ⁻¹' {x}) y hy (2 * d) a = CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) y) :
    fiber_push f x (2 * d) a = Nat.card (f ⁻¹' {x}) • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x := by
  classical
  let K : Set Y := f ⁻¹' {x}
  let : Fintype K := hfinite.fintype
  choose e hy he ho using fun y : K => horientation y.val
  let U : K → Opens Y := fun y => ⟨(e y).source, (e y).open_source⟩
  have hUK : ∀ (y : K) (w : U y), w.val ∈ K → w.val = y.val := by
    intro y w hw
    apply (e y).injOn w.property (hy y)
    exact (he y w.property).trans
      ((show f w.val = x from hw).trans
        ((show f y.val = x from y.property).symm.trans (he y (hy y)).symm))
  rw [← complex_finite_support_decomposition d K U hy hUK a, map_sum]
  calc
    _ = ∑ _y : K, CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x := by
      apply Finset.sum_congr rfl
      intro y _
      rw [ha]
      exact sheet_push_generator f (e y) (fun w hw => (he y hw).symm)
        y.val (hy y) x ((he y (hy y)).trans y.property)
        (fun w hw => Subtype.ext (hUK y w hw)) (ho y)
    _ = Nat.card (f ⁻¹' {x}) • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x := by
      change (∑ _y : K, CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x) = Nat.card K • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := d) x
      simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

variable [CompactSpace X] [CompactSpace Y]

/-- An oriented covering of constant finite positive degree multiplies
the integral fundamental class by that degree. -/
theorem complex_integral_fundamental_map_degree
    (f : TopCat.of Y ⟶ TopCat.of X) (degree : ℕ) (hdegree_pos : 0 < degree)
    (hdegree : ∀ x : X, Nat.card (f ⁻¹' {x}) = degree)
    (hhol : IsLocalDiffeomorph
      𝓘(ℂ, Fin d → ℂ) 𝓘(ℂ, Fin d → ℂ) 1 f) :
    HomologicalComplex.homologyMap (CycleClass.Geometric.LocalHomology.Cycles.integralSingularChainFunctor.map f) (2 * d)
      (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d Y) = degree • CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d X := by
  apply complex_absolute_top_ext d
  intro x
  have hf : Set.MapsTo f (f ⁻¹' {x})ᶜ ({x} : Set X)ᶜ := fun _ hx => hx
  have hp := congrArg (fun g => HomologicalComplex.homologyMap g (2 * d))
    (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection_naturality f hf)
  simp only [HomologicalComplex.homologyMap_comp] at hp
  have hpn := (ConcreteCategory.congr_hom hp (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d Y)).symm
  have hfinite : (f ⁻¹' {x}).Finite := by
    have : Finite (f ⁻¹' {x}) := Nat.finite_of_card_ne_zero
      ((hdegree x).trans_ne (Nat.ne_of_gt hdegree_pos))
    exact Set.toFinite _
  have hlocal := complex_fiber_push_degree f (CoverLocal.CM.holomorphic_cover_orientation f hhol) x hfinite
    (HomologicalComplex.homologyMap
      (CycleClass.Geometric.LocalHomology.Cycles.relativeChainProjection (TopCat.of Y) (f ⁻¹' {x})ᶜ) (2 * d)
      (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d Y))
    (fun y hy => (absolute_support_at_point (TopCat.of Y) (f ⁻¹' {x}) y hy (2 * d)
      (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass d Y)).trans (CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass_atPoint d Y y))
  rw [hdegree x] at hlocal
  rw [map_nsmul, CycleClass.Geometric.CompactManifoldFundamental.Cycles.complexManifoldFundamentalClass_atPoint]
  exact hpn.trans hlocal

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.CoverDegree.CM
