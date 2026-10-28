import OAI.AlgebraicGeometry.CycleClass.Geometric.CenteredChartTransition
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalChartMaps
import OAI.AlgebraicGeometry.CycleClass.Geometric.LocalDerivativeHomology

/-! # Complex Chart Local Action -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartLocalAction

noncomputable section

/-!
# Actual local action of complex chart transitions

A complex differentiable local homeomorphism fixing the origin acts as the
identity on degree `2p` local integral singular homology. The comparison uses
its actual map on a small coordinate ball, the explicit derivative homotopy,
and the proved excision isomorphism. Applying this to genuine centered chart
transitions establishes their action on every top local class.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold _root_.Topology

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

/-- The actual local action of a positive-dimensional complex
differentiable local homeomorphism fixing zero is the identity. -/
theorem positiveComplexDifferentiableLocalHomologyIsoTo_eq_id {p : ℕ} (hp : 0 < p)
    (e : OpenPartialHomeomorph (Fin p → ℂ) (Fin p → ℂ))
    (hsource : (0 : Fin p → ℂ) ∈ e.source) (hzero : e 0 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hd : HasFDerivAt e (L.restrictScalars ℝ : _ →L[ℝ] _) 0) :
    (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      e 0 0 hsource hzero (2 * p)).hom = 𝟙 _ := by
  obtain ⟨r, hr, hc, he, hball, hlocal⟩ :=
    LocalDerivativeHomology.Cycles.exists_complexDerivative_localHomology_eq_excision hp e L hd
      (e.open_source.mem_nhds hsource) e.continuousOn
  let i := LocalExcision.Cycles.localExcisionHomologyIso (TopCat.of (Fin p → ℂ)) (Metric.ball 0 r) 0
    (by simpa using hr) Metric.isOpen_ball (2 * p)
  apply (cancel_epi i.hom).mp
  rw [Category.comp_id]
  change HomologicalComplex.homologyMap
      (LocalExcision.Cycles.localExcisionChainMap (TopCat.of (Fin p → ℂ)) (Metric.ball 0 r) 0 _) (2 * p) ≫
      _ = i.hom
  rw [LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_restriction
    (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
    e (Metric.ball 0 r) hball]
  have hm : LocalChartMaps.Cycles.openPartialRestrictionMap
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      e (Metric.ball 0 r) hball = LocalDerivativeHomology.Cycles.translatedBallMap e r hc := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change e x.val = e x.val - e 0
    rw [hzero, sub_zero]
  have hmap :
      LocalChartMaps.Cycles.injectiveLocalHomologyMapTo
        (LocalChartMaps.Cycles.openPartialRestrictionMap
          (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
          e (Metric.ball 0 r) hball)
        (LocalChartMaps.Cycles.openPartialRestrictionMap_injective
          (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
          e (Metric.ball 0 r) hball)
        (LocalDerivativeHomology.Cycles.ballZero (Fin p → ℂ) r hr) 0 hzero (2 * p) =
      LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap e (L.restrictScalars ℝ) r hr hc he (2 * p) := by
    unfold LocalChartMaps.Cycles.injectiveLocalHomologyMapTo LocalDerivativeHomology.Cycles.translatedBallLocalHomologyMap
    exact LocalChartMaps.Cycles.relativeSingularHomologyMap_congr hm _ _ (2 * p)
  exact hmap.trans hlocal

/-- The degree `2p` local action is the identity also in complex dimension
zero, where the coordinate space is a singleton. -/
theorem complexDifferentiableLocalHomologyIsoTo_eq_id {p : ℕ}
    (e : OpenPartialHomeomorph (Fin p → ℂ) (Fin p → ℂ))
    (hsource : (0 : Fin p → ℂ) ∈ e.source) (hzero : e 0 = 0)
    (L : (Fin p → ℂ) ≃L[ℂ] (Fin p → ℂ))
    (hd : HasFDerivAt e (L.restrictScalars ℝ : _ →L[ℝ] _) 0) :
    (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
      e 0 0 hsource hzero (2 * p)).hom = 𝟙 _ := by
  by_cases hp : p = 0
  · subst p
    exact LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_eq_id (X := TopCat.of (Fin 0 → ℂ)) e 0 hsource
      (fun _ _ => Subsingleton.elim _ _) 0
  · exact positiveComplexDifferentiableLocalHomologyIsoTo_eq_id
      (Nat.pos_of_ne_zero hp) e hsource hzero L hd

variable {p : ℕ} {M : Type} [TopologicalSpace M]
variable (e e' : OpenPartialHomeomorph M (Fin p → ℂ))

/-- The actual local homology isomorphism of the centered transition. -/
def centeredComplexChartLocalHomologyIso (z : Fin p → ℂ)
    (hz : z ∈ (e.symm.trans e').source) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n :=
  LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
    (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
    (CenteredChartTransition.Cycles.centeredComplexChartChange e e' z) 0 0
    (CenteredChartTransition.Cycles.centeredComplexChartChange_zero_mem e e' z hz)
    (CenteredChartTransition.Cycles.centeredComplexChartChange_zero e e' z) n

variable [ChartedSpace (Fin p → ℂ) M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- Every actual complex atlas transition, centered at a point in its
domain, preserves the entire top local homology group. -/
theorem centeredComplexChartLocalHomologyIso_hom_eq_id
    (he : e ∈ atlas (Fin p → ℂ) M) (he' : e' ∈ atlas (Fin p → ℂ) M)
    (z : Fin p → ℂ) (hz : z ∈ (e.symm.trans e').source) :
    (centeredComplexChartLocalHomologyIso e e' z hz (2 * p)).hom = 𝟙 _ :=
  complexDifferentiableLocalHomologyIsoTo_eq_id
    (CenteredChartTransition.Cycles.centeredComplexChartChange e e' z)
    (CenteredChartTransition.Cycles.centeredComplexChartChange_zero_mem e e' z hz)
    (CenteredChartTransition.Cycles.centeredComplexChartChange_zero e e' z)
    (ComplexChartDerivative.Cycles.complexChartTransitionDerivative e e' he he' z hz)
    (CenteredChartTransition.Cycles.centeredComplexChartChange_hasRealFDerivAt e e' he he' z hz)

/-- In particular, every top local class, including any specified
generator, is fixed by the actual centered complex transition. -/
theorem centeredComplexChartLocalHomologyIso_preserves
    (he : e ∈ atlas (Fin p → ℂ) M) (he' : e' ∈ atlas (Fin p → ℂ) M)
    (z : Fin p → ℂ) (hz : z ∈ (e.symm.trans e').source)
    (c : LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 (2 * p)) :
    (centeredComplexChartLocalHomologyIso e e' z hz (2 * p)).hom c = c := by
  rw [centeredComplexChartLocalHomologyIso_hom_eq_id e e' he he' z hz]
  rfl

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartLocalAction
