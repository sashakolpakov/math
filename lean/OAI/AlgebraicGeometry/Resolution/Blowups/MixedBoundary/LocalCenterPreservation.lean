import OAI.AlgebraicGeometry.Resolution.Blowups.NamedModeledMixedCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.BaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartComposition

/-! # Local Center Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LocalCenterPreservation.Construction

noncomputable section

/-! Preserve the complete mixed boundary from a pointed common-coordinate center chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem exists_mixed_boundary_open_chart_of_center_chart
    (R : CommRingCat.{u}) [Algebra k R] (I : Ideal R) {ι : Type v}
    (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I)
    (a : I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (C : CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F
      (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Equations.Construction.blowupMixedBoundaryFamily I a F w hw) p) := by
  let B := C.chart
  have hf : B.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom B.map.toRingHom)))
  obtain ⟨Q, hQ, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a B.map.toRingHom hf p B.point B.point_over
  let a' : I.map B.map.toRingHom := ⟨B.map a.val, Ideal.mem_map_of_mem _ a.property⟩
  have hmodels := B.model.mixed_named_center_preserves_boundary
    (I.map B.map.toRingHom) C.coordinates C.center_eq F C.divided_iff a'
    (fun j hj => Ideal.mem_map_of_mem B.map.toRingHom (hw j hj))
  obtain ⟨D⟩ := hmodels Q
  let f := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a B.map
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion I a B.map.toRingHom
  exact ⟨D.comp f (Equations.Construction.blowupMixedBoundaryFamily I a F w hw)
    (BaseChange.Construction.blowupMixedBoundaryFamily_map I a F w hw B.map.toRingHom) p hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.LocalCenterPreservation.Construction
