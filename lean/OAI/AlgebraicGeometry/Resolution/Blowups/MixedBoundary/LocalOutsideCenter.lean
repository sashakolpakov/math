import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.OutsideCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartComposition
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty

/-! # Local Outside Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LocalOutsideCenter.Construction

noncomputable section

/-! Local source boundary models suffice outside the actual blowup center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (k : Type u) [CommRing k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem exists_local_mixed_boundary_open_chart_outside_center
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {ι : Type v}
    (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (a : I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (hp : ¬ I ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Equations.Construction.blowupMixedBoundaryFamily I a F w hw) p) := by
  obtain ⟨C⟩ := hboundary (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)))
  obtain ⟨Q, hQ, hbase⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a C.map.toRingHom hf p C.point C.point_over
  let a' : I.map C.map.toRingHom := ⟨C.map a.val, Ideal.mem_map_of_mem _ a.property⟩
  have hCI : C.point.asIdeal.comap C.map.toRingHom =
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.point_over
  have hbaseI : Q.asIdeal.comap (Blowup.Charts.Construction.blowupChartConstants (I.map C.map.toRingHom) a') = C.point.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hbase
  have hout : ¬ I.map C.map.toRingHom ≤
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants (I.map C.map.toRingHom) a') Q).asIdeal := by
    change ¬ I.map C.map.toRingHom ≤ Q.asIdeal.comap (Blowup.Charts.Construction.blowupChartConstants (I.map C.map.toRingHom) a')
    rw [hbaseI, Ideal.map_le_iff_le_comap, hCI]
    exact hp
  obtain ⟨B⟩ := OutsideCenter.Construction.exists_mixed_boundary_open_chart_outside_center k C.carrier
    (fun j => C.map (w j)) C.model (I.map C.map.toRingHom) a' F
    (fun j hj => Ideal.mem_map_of_mem C.map.toRingHom (hw j hj)) Q hout
  let f := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a C.map
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion I a C.map.toRingHom
  exact ⟨B.comp f (Equations.Construction.blowupMixedBoundaryFamily I a F w hw)
    (BaseChange.Construction.blowupMixedBoundaryFamily_map I a F w hw C.map.toRingHom) p hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LocalOutsideCenter.Construction
