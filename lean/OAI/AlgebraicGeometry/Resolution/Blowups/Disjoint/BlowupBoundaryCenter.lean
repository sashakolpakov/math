import OAI.AlgebraicGeometry.Resolution.Blowups.UnitBlowupOtherCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.OutsideCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.ControlledTransformMap

/-! # Blowup Boundary Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A disjoint remaining center retains all old boundary coordinates and the new exceptional unit label. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.disjointBlowup
    {k : Type u} [CommRing k] (R : CommRingCat.{u}) [Algebra k R]
    (K L : Ideal R) (a : K) {ι : Type v} (w : ι → R) (F G : Finset ι)
    (hw : ∀ j ∈ F, w j ∈ K) (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R L w G)
    (hdisjoint : K ⊔ L = ⊤) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k (.of (Blowup.Charts.Construction.blowupChart K a)) (L.map (Blowup.Charts.Construction.blowupChartConstants K a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily K a F w hw) (G.map Function.Embedding.some) := by
  intro p hp
  have hLp : L ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants K a) p).asIdeal :=
    Ideal.map_le_iff_le_comap.mp hp
  have hKp : ¬ K ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants K a) p).asIdeal := by
    intro hK
    have ht := sup_le hK hLp
    rw [hdisjoint] at ht
    exact (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants K a) p).isPrime.ne_top (top_le_iff.mp ht)
  let S := Localization.Away a.val
  let φ : R →ₐ[k] S := IsScalarTower.toAlgHom k R S
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom)) := IsOpenImmersion.of_isLocalization a.val
  have hφ : φ.toRingHom.Etale := RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway a.val)
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a.val (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants K a) p)
    (Boundary.OutsideCenter.Construction.blowupChart_denominator_not_mem_of_outside K a p hKp)
  obtain ⟨Q, hQ, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime K a φ.toRingHom hφ p q hq
  let a' : K.map φ.toRingHom := ⟨φ a.val, Ideal.mem_map_of_mem _ a.property⟩
  have ha' : IsUnit a'.val := IsLocalization.Away.algebraMap_isUnit a.val
  let ψ := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k K a φ
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom ψ.toRingHom)) :=
    Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion K a φ.toRingHom
  have hc := (h.etale_baseChange (S := .of S) φ hφ).unitDenominatorBlowup (.of S)
    (K.map φ.toRingHom) (L.map φ.toRingHom) a' ha' (fun j => φ (w j)) F G
    (fun j hj => Ideal.mem_map_of_mem φ.toRingHom (hw j hj))
  have hfamily : (fun j => ψ (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily K a F w hw j)) =
      MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily (K.map φ.toRingHom) a' F (fun j => φ (w j))
        (fun j hj => Ideal.mem_map_of_mem φ.toRingHom (hw j hj)) := by
    funext j
    exact MixedBoundary.BaseChange.Construction.blowupMixedBoundaryFamily_map K a F w hw φ.toRingHom j
  have hc' : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k (.of (Blowup.Charts.Construction.blowupChart (K.map φ.toRingHom) a'))
      ((L.map (Blowup.Charts.Construction.blowupChartConstants K a)).map ψ.toRingHom)
      (fun j => ψ (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily K a F w hw j)) (G.map Function.Embedding.some) := by
    rw [hfamily]
    change MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k (.of (Blowup.Charts.Construction.blowupChart (K.map φ.toRingHom) a'))
      ((L.map (Blowup.Charts.Construction.blowupChartConstants K a)).map (ChartLift.Construction.blowupChartMap K φ.toRingHom a)) _ _
    rw [ControlledTransformMap.Construction.blowupChartMap_totalIdeal]
    exact hc
  have hLQ : (L.map (Blowup.Charts.Construction.blowupChartConstants K a)).map ψ.toRingHom ≤ Q.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    have he := congrArg PrimeSpectrum.asIdeal hQ
    change Q.asIdeal.comap ψ.toRingHom = p.asIdeal at he
    rw [he]
    exact hp
  obtain ⟨C⟩ := hc' Q hLQ
  exact ⟨C.comp (R := .of (Blowup.Charts.Construction.blowupChart K a)) (S := .of (Blowup.Charts.Construction.blowupChart (K.map φ.toRingHom) a'))
    (L.map (Blowup.Charts.Construction.blowupChartConstants K a))
    (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily K a F w hw) (G.map Function.Embedding.some) ψ p hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
