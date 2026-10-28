import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocallyFiniteFundamental
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocallyFiniteRestrictionNaturality
import Mathlib.Geometry.Manifold.Diffeomorph

/-! # Complex Fundamental Naturality -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles

noncomputable section

/-!
# Naturality of the canonical complex fundamental classes

The centered coordinate map of a complex diffeomorphism has an actual
invertible complex derivative. Its proved local homology action preserves
the canonical complex generator. Compact and locally finite fundamental
class naturality then follows from their proved local uniqueness.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A translation and its inverse are genuinely complex differentiable. -/
theorem complexTranslation_mdifferentiable {p : ℕ} (v : Fin p → ℂ) :
    (Homeomorph.addRight v).toOpenPartialHomeomorph.MDifferentiable
      𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) := by
  constructor
  · exact ((differentiable_id (𝕜 := ℂ)).add_const v).mdifferentiable.mdifferentiableOn
  · exact ((differentiable_id (𝕜 := ℂ)).add_const (-v)).mdifferentiable.mdifferentiableOn

/-- Bidifferentiability supplies the actual complex derivative equivalence,
so the earlier derivative-homotopy theorem applies without assumed local degree. -/
theorem complexMDifferentiableLocalHomologyIsoTo_eq_id {p : ℕ}
    (e : OpenPartialHomeomorph (Fin p → ℂ) (Fin p → ℂ))
    (he : e.MDifferentiable 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ))
    (hsource : (0 : Fin p → ℂ) ∈ e.source) (hzero : e 0 = 0) :
    (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      e 0 0 hsource hzero (2 * p)).hom = 𝟙 _ := by
  let L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ) := he.mfderiv hsource
  have hL : (L : (Fin p → ℂ) →L[ℂ] (Fin p → ℂ)) = fderiv ℂ e 0 := mfderiv_eq_fderiv
  have hd : HasFDerivAt e (L : (Fin p → ℂ) →L[ℂ] (Fin p → ℂ)) 0 := by
    rw [hL]
    exact (he.mdifferentiableAt hsource).differentiableAt.hasFDerivAt
  exact ComplexChartLocalAction.Cycles.complexDifferentiableLocalHomologyIsoTo_eq_id e hsource hzero L (hd.restrictScalars ℝ)

/-- For a global homeomorphism, the pointed partial-map construction is
the ordinary map of the actual punctured pairs. -/
theorem homeomorph_pointedLocalHomology_hom {X Y : TopCat.{0}} [T1Space X] [T1Space Y]
    (e : X ≃ₜ Y) (x : X) (n : ℕ) :
    (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo e.toOpenPartialHomeomorph x (e x)
      (mem_univ x) rfl n).hom = (LocalHomology.Cycles.localSingularHomologyIso e x n).hom := by
  rw [LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_eq_map e.toOpenPartialHomeomorph
    (TopCat.isoOfHomeo e).hom e.injective x (e x) (mem_univ x) rfl rfl (fun _ _ => rfl)]
  rfl

variable {p : ℕ} {M N : Type} [TopologicalSpace M] [TopologicalSpace N]
variable [T2Space M] [T2Space N]
variable [ChartedSpace (Fin p → ℂ) M] [ChartedSpace (Fin p → ℂ) N]
variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 N]

omit [T2Space M] in
/-- Centering a complex atlas chart preserves its genuine bidifferentiability. -/
theorem centeredComplexChart_mdifferentiable
    (e : OpenPartialHomeomorph M (Fin p → ℂ)) (he : e ∈ atlas (Fin p → ℂ) M) (x : M) :
    (CenteredChartTransition.Cycles.centeredLocalChart e x).MDifferentiable 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) := by
  unfold CenteredChartTransition.Cycles.centeredLocalChart
  rw [OpenPartialHomeomorph.transHomeomorph_eq_trans]
  exact (mdifferentiable_of_mem_atlas (I := 𝓘(ℂ, Fin p → ℂ)) he).trans
    (complexTranslation_mdifferentiable (-(e x)))

/-- The actual local map of a complex diffeomorphism is compatible with
the canonical centered-chart top-local-homology identifications. -/
theorem complexDiffeomorph_chart_localHomology
    (f : Diffeomorph 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) M N 1)
    (e : OpenPartialHomeomorph M (Fin p → ℂ)) (he : e ∈ atlas (Fin p → ℂ) M)
    (e' : OpenPartialHomeomorph N (Fin p → ℂ)) (he' : e' ∈ atlas (Fin p → ℂ) N)
    (x : M) (hx : x ∈ e.source) (hfx : f x ∈ e'.source) :
    (LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph x (2 * p)).hom ≫
        (ComplexChartOrientation.Cycles.complexChartLocalIso e' (f x) hfx (2 * p)).hom =
      (ComplexChartOrientation.Cycles.complexChartLocalIso e x hx (2 * p)).hom := by
  let a := CenteredChartTransition.Cycles.centeredLocalChart e x
  let b := CenteredChartTransition.Cycles.centeredLocalChart e' (f x)
  let g := f.toHomeomorph.toOpenPartialHomeomorph
  have ha : x ∈ a.source := hx
  have hb : f x ∈ b.source := hfx
  have ha0 : a x = 0 := CenteredChartTransition.Cycles.centeredLocalChart_at_point e x
  have hb0 : b (f x) = 0 := CenteredChartTransition.Cycles.centeredLocalChart_at_point e' (f x)
  have has : (0 : Fin p → ℂ) ∈ a.target := by
    rw [← ha0]
    exact a.map_source ha
  have hai : a.symm 0 = x := by rw [← ha0]; exact a.left_inv ha
  let c := a.symm.trans (g.trans b)
  have hc0 : (0 : Fin p → ℂ) ∈ c.source := by
    refine ⟨has, ?_⟩
    change a.symm 0 ∈ (g.trans b).source
    rw [hai]
    exact ⟨mem_univ x, hb⟩
  have hcz : c 0 = 0 := by
    change b (g (a.symm 0)) = 0
    rw [hai]
    exact hb0
  have hc : c.MDifferentiable 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) :=
    (centeredComplexChart_mdifferentiable e he x).symm.trans
      ((f.toOpenPartialHomeomorph_mdifferentiable one_ne_zero).trans
        (centeredComplexChart_mdifferentiable e' he' (f x)))
  have hcomp :
      (ComplexChartOrientation.Cycles.complexChartLocalIso e x hx (2 * p)).inv ≫
        (LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
          f.toHomeomorph x (2 * p)).hom ≫
        (ComplexChartOrientation.Cycles.complexChartLocalIso e' (f x) hfx (2 * p)).hom =
      (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
        (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
        c 0 0 hc0 hcz (2 * p)).hom := by
    change (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) a x 0 ha ha0 (2 * p)).inv ≫
        (LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
          f.toHomeomorph x (2 * p)).hom ≫
        (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
          (X := TopCat.of N) (Y := TopCat.of (Fin p → ℂ)) b (f x) 0 hb hb0 (2 * p)).hom = _
    erw [← LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_symm_hom
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ)) a x 0 ha ha0 (2 * p)]
    erw [← homeomorph_pointedLocalHomology_hom
      (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph x (2 * p)]
    erw [LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_comp
      (X := TopCat.of M) (Y := TopCat.of N) (Z := TopCat.of (Fin p → ℂ))
      g b x (f x) 0 (mem_univ x) hb rfl hb0 (2 * p)]
    have hgb : x ∈ (g.trans b).source := ⟨mem_univ x, hb⟩
    have hgb0 : (g.trans b) x = 0 := hb0
    erw [LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_comp
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of M) (Z := TopCat.of (Fin p → ℂ))
      a.symm (g.trans b) 0 x 0 has hgb hai hgb0 (2 * p)]
  apply (cancel_epi (ComplexChartOrientation.Cycles.complexChartLocalIso e x hx (2 * p)).inv).mp
  rw [hcomp, complexMDifferentiableLocalHomologyIsoTo_eq_id c hc hc0 hcz, Iso.inv_hom_id]

/-- A complex diffeomorphism preserves the actual canonical local generator. -/
theorem complexCanonicalLocalClass_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) M N 1) (x : M) :
    (LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
      f.toHomeomorph x (2 * p)).hom (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) =
      ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) (f x) := by
  let e := chartAt (Fin p → ℂ) x
  let e' := chartAt (Fin p → ℂ) (f x)
  have hx : x ∈ e.source := mem_chart_source (Fin p → ℂ) x
  have hfx : f x ∈ e'.source := mem_chart_source (Fin p → ℂ) (f x)
  apply (ConcreteCategory.bijective_of_isIso (ComplexChartOrientation.Cycles.complexChartLocalIso e' (f x) hfx (2 * p)).hom).1
  change ((LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
    f.toHomeomorph x (2 * p)).hom ≫ (ComplexChartOrientation.Cycles.complexChartLocalIso e' (f x) hfx (2 * p)).hom)
      (ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) = _
  rw [complexDiffeomorph_chart_localHomology f e (chart_mem_atlas _ _) e' (chart_mem_atlas _ _)
    x hx hfx, ComplexChartOrientation.Cycles.complexChartLocalIso_canonical e (chart_mem_atlas _ _) x hx,
    ComplexChartOrientation.Cycles.complexChartLocalIso_canonical e' (chart_mem_atlas _ _) (f x) hfx]

/-- A complex diffeomorphism transports the canonical compact-support
fundamental class by its actual map of complementary pairs. -/
theorem complexCompactFundamentalClass_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) M N 1)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hmap : ∀ x, x ∈ K ↔ f.toHomeomorph x ∈ L) :
    (CompactSupportCharts.Cycles.homeomorphSupportHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
      f.toHomeomorph K L hmap (2 * p)).hom (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK) =
        ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p L hL := by
  apply ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_unique p L hL
  intro y hy
  obtain ⟨x, rfl⟩ := f.toHomeomorph.surjective y
  have hx : x ∈ K := (hmap x).mpr hy
  have ht := ConcreteCategory.congr_hom
    (CompactSupportCharts.Cycles.homeomorphSupportHomologyIso_toPoint (X := TopCat.of M) (Y := TopCat.of N)
      f.toHomeomorph K L hmap (2 * p) x hx) (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK)
  change LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of N) L (f.toHomeomorph x) _ (2 * p)
      ((CompactSupportCharts.Cycles.homeomorphSupportHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
        f.toHomeomorph K L hmap (2 * p)).hom (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK)) =
    (LocalHomology.Cycles.localSingularHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
      f.toHomeomorph x (2 * p)).hom
        (LocalHomologyPresheaf.Cycles.localHomologyToPoint (TopCat.of M) K x hx (2 * p)
          (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK)) at ht
  rw [ComplexCompactFundamental.Cycles.complexCompactFundamentalClass_atPoint] at ht
  exact ht.trans (complexCanonicalLocalClass_diffeomorph f x)

/-- The corresponding compact-support statement for a homeomorphism
with complex C1 forward and inverse maps. -/
theorem complexCompactFundamentalClass_homeomorph (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1 e)
    (hei : ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1 e.symm)
    (K : Set M) (L : Set N) (hK : IsCompact K) (hL : IsCompact L)
    (hmap : ∀ x, x ∈ K ↔ e x ∈ L) :
    (CompactSupportCharts.Cycles.homeomorphSupportHomologyIso (X := TopCat.of M) (Y := TopCat.of N)
      e K L hmap (2 * p)).hom (ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p K hK) =
        ComplexCompactFundamental.Cycles.complexCompactFundamentalClass p L hL := by
  let f : Diffeomorph 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) M N 1 :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  exact complexCompactFundamentalClass_diffeomorph f K L hK hL hmap

variable [SecondCountableTopology M] [SecondCountableTopology N]

/-- The canonical locally finite fundamental class is natural under the
actual proper pushforward of a complex diffeomorphism. -/
theorem complexLocallyFiniteFundamentalClass_diffeomorph
    (f : Diffeomorph 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) M N 1) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) f.toHomeomorph).hom
      f.toHomeomorph.isProperMap (2 * p) (ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass p M) =
        ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass p N := by
  apply ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteHomology_compact_ext p N
  intro L hL
  rw [LocallyFiniteRestrictionNaturality.Cycles.locallyFiniteCompactHomologyRestriction_naturality_apply,
    ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_restriction,
    ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass_restriction]
  exact complexCompactFundamentalClass_diffeomorph f (f.toHomeomorph ⁻¹' L) L
    (f.toHomeomorph.isProperMap.isCompact_preimage hL) hL (fun _ => Iff.rfl)

/-- The same naturality for a homeomorphism with complex C1 inverse;
properness follows from being an actual homeomorphism. -/
theorem complexLocallyFiniteFundamentalClass_homeomorph (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1 e)
    (hei : ContMDiff 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) 1 e.symm) :
    LocallyFiniteProperMap.Cycles.locallyFiniteProperHomologyMap ℤ
      (TopCat.isoOfHomeo (X := TopCat.of M) (Y := TopCat.of N) e).hom e.isProperMap (2 * p)
        (ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass p M) =
      ComplexLocallyFiniteFundamental.Cycles.complexLocallyFiniteFundamentalClass p N := by
  let f : Diffeomorph 𝓘(ℂ, Fin p → ℂ) 𝓘(ℂ, Fin p → ℂ) M N 1 :=
    { toEquiv := e.toEquiv
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  exact complexLocallyFiniteFundamentalClass_diffeomorph f

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexFundamentalNaturality.Cycles
