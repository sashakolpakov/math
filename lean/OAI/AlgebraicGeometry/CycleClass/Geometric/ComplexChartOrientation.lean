import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartLocalAction
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexLocalTopHomology

/-! # Complex Chart Orientation -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation

noncomputable section

/-!
# Chart-independent complex local generators

A chart followed by translation to the origin identifies local homology
with the computed coordinate model. The actual transition between any two
complex atlas charts acts identically on top local homology, so the
resulting local generator is independent of the chart. No global fundamental
class or sheaf gluing theorem is asserted here.
-/

open _root_.CategoryTheory
open scoped _root_.Manifold

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Cycles

variable {p : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin p → ℂ) M]

/-- The actual local chart isomorphism obtained by centering that chart. -/
def complexChartLocalIso (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source) (n : ℕ) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x n ≅
      LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin p → ℂ)) 0 n := by
  letI : T1Space M := ChartedSpace.t1Space (Fin p → ℂ) M
  exact LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
    (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))
    (CenteredChartTransition.Cycles.centeredLocalChart e x) x 0 hx (CenteredChartTransition.Cycles.centeredLocalChart_at_point e x) n

/-- The computed coordinate normalization after the actual centered chart. -/
def complexChartTopLocalIso (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * p) ≅ ModuleCat.of ℤ ℤ :=
  complexChartLocalIso e x hx (2 * p) ≪≫ ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyIso p

/-- The local generator specified by an actual centered chart. -/
def complexChartLocalClass (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source) : LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * p) :=
  (complexChartTopLocalIso e x hx).toLinearEquiv.symm 1

@[simp]
theorem complexChartLocalClass_normalization (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source) :
    (complexChartTopLocalIso e x hx).toLinearEquiv (complexChartLocalClass e x hx) = 1 :=
  (complexChartTopLocalIso e x hx).toLinearEquiv.apply_symm_apply 1

theorem complexChartLocalClass_ne_zero (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source) : complexChartLocalClass e x hx ≠ 0 := by
  intro h
  have hn := complexChartLocalClass_normalization e x hx
  rw [h, map_zero] at hn
  exact zero_ne_one hn

/-- Every local top class has a unique integer coefficient in this chart. -/
theorem complexChartLocalClass_generates (e : OpenPartialHomeomorph M (Fin p → ℂ))
    (x : M) (hx : x ∈ e.source)
    (c : LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * p)) :
    ∃! a : ℤ, a • complexChartLocalClass e x hx = c := by
  let q := (complexChartTopLocalIso e x hx).toLinearEquiv
  have hnorm (a : ℤ) : q (a • complexChartLocalClass e x hx) = a := by
    calc
      q (a • complexChartLocalClass e x hx) = a • q (complexChartLocalClass e x hx) :=
        map_zsmul q.toLinearMap _ _
      _ = a := by
        change a • ((complexChartTopLocalIso e x hx).toLinearEquiv
          (complexChartLocalClass e x hx)) = a
        rw [complexChartLocalClass_normalization]
        simp
  refine ⟨q c, ?_, ?_⟩
  · apply q.injective
    exact hnorm _
  · intro a ha
    rw [← hnorm a, ha]

/-- The local complex class defined using the preferred atlas chart;
chart independence is proved below from actual transition maps. -/
def complexCanonicalLocalClass (x : M) :
    LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * p) :=
  complexChartLocalClass (chartAt (Fin p → ℂ) x) x (mem_chart_source (Fin p → ℂ) x)

theorem complexCanonicalLocalClass_ne_zero (x : M) :
    complexCanonicalLocalClass (p := p) x ≠ 0 :=
  complexChartLocalClass_ne_zero (chartAt (Fin p → ℂ) x) x
    (mem_chart_source (Fin p → ℂ) x)

theorem complexCanonicalLocalClass_generates (x : M)
    (c : LocalHomology.Cycles.localSingularHomology (TopCat.of M) x (2 * p)) :
    ∃! a : ℤ, a • complexCanonicalLocalClass (p := p) x = c :=
  complexChartLocalClass_generates (chartAt (Fin p → ℂ) x) x
    (mem_chart_source (Fin p → ℂ) x) c

variable [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

/-- The actual top local homology comparison is independent of which
complex atlas chart is centered at the point. -/
theorem complexChartLocalIso_hom_eq
    (e e' : OpenPartialHomeomorph M (Fin p → ℂ))
    (he : e ∈ atlas (Fin p → ℂ) M) (he' : e' ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    (complexChartLocalIso e x hx (2 * p)).hom =
      (complexChartLocalIso e' x hx' (2 * p)).hom := by
  have : T1Space M := ChartedSpace.t1Space (Fin p → ℂ) M
  change (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))
      (CenteredChartTransition.Cycles.centeredLocalChart e x) x 0 hx (CenteredChartTransition.Cycles.centeredLocalChart_at_point e x) (2 * p)).hom =
    (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))
      (CenteredChartTransition.Cycles.centeredLocalChart e' x) x 0 hx' (CenteredChartTransition.Cycles.centeredLocalChart_at_point e' x) (2 * p)).hom
  apply (cancel_epi (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo
      (X := TopCat.of M) (Y := TopCat.of (Fin p → ℂ))
      (CenteredChartTransition.Cycles.centeredLocalChart e x) x 0 hx (CenteredChartTransition.Cycles.centeredLocalChart_at_point e x) (2 * p)).inv).mp
  rw [Iso.inv_hom_id]
  symm
  rw [← LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_symm_hom,
    LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_comp]
  calc
    _ = (ComplexChartLocalAction.Cycles.centeredComplexChartLocalHomologyIso e e' (e x)
        (ComplexChartDerivative.Cycles.complexChartTransition_mem_source e e' x hx hx') (2 * p)).hom := by
      exact congrArg Iso.hom (LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_congr
        (X := TopCat.of (Fin p → ℂ)) (Y := TopCat.of (Fin p → ℂ))
        (CenteredChartTransition.Cycles.centeredLocalChart_transition e e' x hx) 0 0 _ _ _ _ (2 * p))
    _ = 𝟙 _ := ComplexChartLocalAction.Cycles.centeredComplexChartLocalHomologyIso_hom_eq_id e e' he he' (e x)
      (ComplexChartDerivative.Cycles.complexChartTransition_mem_source e e' x hx hx')

/-- The resulting normalized local generator is independent of the atlas
chart. -/
theorem complexChartLocalClass_eq
    (e e' : OpenPartialHomeomorph M (Fin p → ℂ))
    (he : e ∈ atlas (Fin p → ℂ) M) (he' : e' ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    complexChartLocalClass e x hx = complexChartLocalClass e' x hx' := by
  have h : complexChartLocalIso e x hx (2 * p) =
      complexChartLocalIso e' x hx' (2 * p) :=
    Iso.ext (complexChartLocalIso_hom_eq e e' he he' x hx hx')
  simp only [complexChartLocalClass, complexChartTopLocalIso, h]

theorem complexChartLocalClass_eq_canonical
    (e : OpenPartialHomeomorph M (Fin p → ℂ)) (he : e ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ e.source) :
    complexChartLocalClass e x hx = complexCanonicalLocalClass (p := p) x :=
  complexChartLocalClass_eq e (chartAt (Fin p → ℂ) x) he
    (chart_mem_atlas (Fin p → ℂ) x) x hx (mem_chart_source (Fin p → ℂ) x)

/-- Every actual complex atlas chart sends the canonical local class to
the same specified coordinate generator. -/
theorem complexChartLocalIso_canonical
    (e : OpenPartialHomeomorph M (Fin p → ℂ)) (he : e ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ e.source) :
    (complexChartLocalIso e x hx (2 * p)).hom (complexCanonicalLocalClass (p := p) x) =
      (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p).symm 1 := by
  apply (ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p).injective
  rw [LinearEquiv.apply_symm_apply]
  change (complexChartTopLocalIso e x hx).toLinearEquiv
    (complexCanonicalLocalClass (p := p) x) = 1
  rw [← complexChartLocalClass_eq_canonical e he x hx,
    complexChartLocalClass_normalization]

end Cycles

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexChartOrientation
