import OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RealModelCharts
import OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison

/-! # Rechart Local Class -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartLocalClass.CM

noncomputable section

section

/-! ThetaCycle: exact local homology maps under the linear change of chart model. -/

open _root_.CategoryTheory Set
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison.Cycles
open scoped _root_.Manifold

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace M] [T1Space M]

def centeredChartLocalIso (a : OpenPartialHomeomorph M E) (x : M)
    (hx : x ∈ a.source) (n : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of M) x n ≅ CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n :=
  CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of M) (Y := TopCat.of E)
    (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart a x) x 0 hx (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_at_point a x) n

def linearOriginLocalIso (e : E ≃L[ℝ] F) (n : ℕ) :
    CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of E) 0 n ≅ CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of F) 0 n :=
  CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of E) (Y := TopCat.of F)
    e.toHomeomorph.toOpenPartialHomeomorph 0 0 (mem_univ 0) e.map_zero n

omit [T1Space M] in
theorem linear_recharted_centered_chart (a : OpenPartialHomeomorph M E)
    (e : E ≃L[ℝ] F) (x : M) :
    CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart (a.trans e.toHomeomorph.toOpenPartialHomeomorph) x =
      (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart a x).trans e.toHomeomorph.toOpenPartialHomeomorph := by
  apply OpenPartialHomeomorph.ext
  · intro y
    simpa only [CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_apply, mfld_simps] using! (e.map_sub (a y) (a x)).symm
  · intro y
    simp only [CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_symm_apply, mfld_simps]
    change a.symm (e.symm (y + e (a x))) = a.symm (e.symm y + a x)
    rw [map_add, e.symm_apply_apply]
  · simp only [CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_source, mfld_simps]

theorem linear_recharted_centered_iso (a : OpenPartialHomeomorph M E)
    (e : E ≃L[ℝ] F) (x : M) (hx : x ∈ a.source) (n : ℕ) :
    (centeredChartLocalIso (a.trans e.toHomeomorph.toOpenPartialHomeomorph) x
      (by simpa only [mfld_simps] using hx) n).hom =
      (centeredChartLocalIso a x hx n).hom ≫ (linearOriginLocalIso e n).hom := by
  symm
  have hxc : x ∈ (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart a x).source := hx
  change (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of M) (Y := TopCat.of E)
      (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart a x) x 0 hxc (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_at_point a x) n).hom ≫
    (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of E) (Y := TopCat.of F)
      e.toHomeomorph.toOpenPartialHomeomorph 0 0 (mem_univ 0) e.map_zero n).hom = _
  erw [CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_comp]
  exact congrArg Iso.hom (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_congr
    (X := TopCat.of M) (Y := TopCat.of F)
    (linear_recharted_centered_chart a e x).symm x 0 _ _ _ _ n)

omit [NormedSpace ℝ E] in
theorem centered_chart_iso_translation (a : OpenPartialHomeomorph M E)
    (x : M) (hx : x ∈ a.source) (n : ℕ) :
    (centeredChartLocalIso a x hx n).hom =
      (CycleClass.Geometric.LocalHomologyCharts.Cycles.openPartialHomeomorphLocalHomologyIso (X := TopCat.of M) (Y := TopCat.of E)
        a x hx n).hom ≫ (CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso E (a x) n).hom := by
  let t := (Homeomorph.subRight (a x)).toOpenPartialHomeomorph
  have ht : a x ∈ t.source := mem_univ _
  have ht0 : t (a x) = 0 := sub_self _
  have hmap : (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo (X := TopCat.of E) (Y := TopCat.of E)
      t (a x) 0 ht ht0 n).hom = (CycleClass.Geometric.ClosedBall.Cycles.localTranslationHomologyIso E (a x) n).hom := by
    rw [CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_eq_map t
      (TopCat.isoOfHomeo (X := TopCat.of E) (Y := TopCat.of E) (Homeomorph.subRight (a x))).hom
      (Homeomorph.subRight (a x)).injective (a x) 0 ht ht0 (sub_self _)
      (fun _ _ => rfl) n]
    rfl
  have hchart : a.trans t = CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart a x := by
    apply OpenPartialHomeomorph.ext
    · intro y
      simp only [t, mfld_simps, CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_apply]
      rfl
    · intro y
      simp only [t, mfld_simps, CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_symm_apply]
      rfl
    · simp only [t, mfld_simps, CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_source]
  have h := CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_comp (X := TopCat.of M) (Y := TopCat.of E)
    (Z := TopCat.of E) a t x (a x) 0 hx ht rfl ht0 n
  rw [hmap] at h
  have hc := congrArg Iso.hom (CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo_congr
    (X := TopCat.of M) (Y := TopCat.of E) hchart x 0
    ⟨hx, ht⟩ hx ht0 (CycleClass.Geometric.CenteredChartTransition.Cycles.centeredLocalChart_at_point a x) n)
  have h' := h.trans hc
  simpa only [centeredChartLocalIso, CycleClass.Geometric.LocalChartMaps.Cycles.openPartialLocalHomologyIsoTo,
    CycleClass.Geometric.LocalChartMaps.Cycles.localPointEqIso, eqToIso_refl, Iso.trans_hom, Iso.refl_hom, Category.comp_id] using! h'.symm

end

/-! ThetaCycle: every fixed real coordinate class is an explicitly derived
integer multiple of the canonical complex local class, uniformly in all
actual complex atlas charts. No generator normalization is assumed. -/

open _root_.CategoryTheory
open OAI.AlgebraicGeometry.CycleClass.Geometric.ComplexCoordinateComparison.Cycles
open scoped _root_.Manifold

def rechartedModelCoefficient (p : ℕ)
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ))
    (v : CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (2 * p) → ℝ)) 0 (2 * p)) : ℤ :=
  CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p ((linearOriginLocalIso e (2 * p)).inv v)

theorem recharted_model_coefficient_class (p : ℕ)
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ))
    (v : CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (2 * p) → ℝ)) 0 (2 * p)) :
    rechartedModelCoefficient p e v • (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p).symm 1 =
      (linearOriginLocalIso e (2 * p)).inv v := by
  apply (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p).injective
  rw [map_zsmul, LinearEquiv.apply_symm_apply]
  simp only [zsmul_eq_mul, mul_one, Int.cast_id, rechartedModelCoefficient]

variable {p : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin p → ℂ) M]
  [T1Space M] [IsManifold 𝓘(ℂ, Fin p → ℂ) 1 M]

theorem linear_recharted_local_class_eq_multiple
    (e : (Fin p → ℂ) ≃L[ℝ] (Fin (2 * p) → ℝ))
    (a : OpenPartialHomeomorph M (Fin p → ℂ)) (ha : a ∈ atlas (Fin p → ℂ) M)
    (x : M) (hx : x ∈ a.source)
    (v : CycleClass.Geometric.LocalHomology.Cycles.localSingularHomology (TopCat.of (Fin (2 * p) → ℝ)) 0 (2 * p)) :
    (centeredChartLocalIso (a.trans e.toHomeomorph.toOpenPartialHomeomorph) x
      (by simpa only [mfld_simps] using hx) (2 * p)).inv v =
      rechartedModelCoefficient p e v • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x := by
  let q := centeredChartLocalIso (a.trans e.toHomeomorph.toOpenPartialHomeomorph) x
    (by simpa only [mfld_simps] using hx) (2 * p)
  have hc : (centeredChartLocalIso a x hx (2 * p)).hom
      (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) =
      (CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p).symm 1 := by
    simpa only [centeredChartLocalIso, CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartLocalIso] using!
      CycleClass.Geometric.ComplexChartOrientation.Cycles.complexChartLocalIso_canonical a ha x hx
  have hq : q.hom (CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x) =
      (linearOriginLocalIso e (2 * p)).hom ((CycleClass.Geometric.ComplexLocalTopHomology.Cycles.complexNormalTopLocalHomologyEquiv p).symm 1) := by
    change (centeredChartLocalIso _ x _ (2 * p)).hom _ = _
    rw [linear_recharted_centered_iso]
    change (linearOriginLocalIso e (2 * p)).hom
      ((centeredChartLocalIso a x hx (2 * p)).hom _) = _
    rw [hc]
  apply q.toLinearEquiv.injective
  change q.hom (q.inv v) = q.hom (_ • CycleClass.Geometric.ComplexChartOrientation.Cycles.complexCanonicalLocalClass (p := p) x)
  rw [Iso.inv_hom_id_apply, map_zsmul, hq, ← map_zsmul,
    recharted_model_coefficient_class, Iso.inv_hom_id_apply]

end

end OAI.AlgebraicGeometry.HodgeConjecture.ThetaCycle.RechartLocalClass.CM
