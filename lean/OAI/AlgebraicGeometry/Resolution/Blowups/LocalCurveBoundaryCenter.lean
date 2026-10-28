import OAI.AlgebraicGeometry.Resolution.Blowups.Modeled.CurveBoundaryCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterGeneralization
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.LocalSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.PointOverClosedPoint
import OAI.AlgebraicGeometry.Resolution.Blowups.Affine.OpenDimension

/-! # Local Curve Boundary Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! The intrinsic curve center is compatible with the full local boundary at every prime. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.curve_center_chart_at_closed_point
    {k : Type u} [Field k] [IsAlgClosed k] {R : CommRingCat.{u}}
    [Algebra k R] [Algebra ℚ R] {β : Type v} [Fintype β] {w : β → R}
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (hd : ringKrullDim R ≤ 1)
    (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤)
    (q : Ideal R) [q.IsMaximal] (hIq : I ≤ q) :
    ∃ F : Finset β, Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F ⟨q, inferInstance⟩) := by
  let : Algebra.Smooth k R := hboundary.smooth
  obtain ⟨C⟩ := hboundary ⟨q, inferInstance⟩
  let : Algebra ℚ C.carrier := (C.map.toRingHom.comp (algebraMap ℚ R)).toAlgebra
  have hc : C.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom C.map.toRingHom)).mp inferInstance
  obtain ⟨Q, hQmax, hQ⟩ := PointOverClosedPoint.Construction.exists_maximal_point_over_closed_point C.map.toRingHom q C.point
    (congrArg PrimeSpectrum.asIdeal C.point_over)
  let : Q.IsMaximal := hQmax
  have hIQ : I.map C.map.toRingHom ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, hQ]
    exact hIq
  have hI' : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (I.map C.map.toRingHom) = ⊤ := by
    have h := Blowups.Smooth.DifferentialMap.Construction.smooth_iteratedRelativeDifferentialIdeal_map k C.map hc I 1
    change (Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I).map C.map.toRingHom =
      Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k (I.map C.map.toRingHom) at h
    rw [hI, Ideal.map_top] at h
    exact h.symm
  obtain ⟨F, M⟩ := C.model.curve_center_chart
    ((Affine.OpenDimension.Construction.ringKrullDim_le_of_spec_openImmersion C.map.toRingHom).trans hd)
    (I.map C.map.toRingHom) hI' Q hIQ
  obtain ⟨M⟩ := M
  exact ⟨F, ⟨M.comp (R := R) (S := C.carrier) I w F C.map ⟨q, inferInstance⟩
    (PrimeSpectrum.ext hQ)⟩⟩

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.curve_center_chart
    {k : Type u} [Field k] [IsAlgClosed k] {R : CommRingCat.{u}}
    [Algebra k R] [Algebra ℚ R] {β : Type v} [Fintype β] {w : β → R}
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w) (hd : ringKrullDim R ≤ 1)
    (I : Ideal R) (hI : Relative.DifferentialBlowup.Construction.firstRelativeDifferentialIdeal k I = ⊤)
    (p : PrimeSpectrum R) (hp : I ≤ p.asIdeal) :
    ∃ F : Finset β, Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p) := by
  obtain ⟨q, hq, hpq⟩ := Ideal.exists_le_maximal p.asIdeal p.isPrime.ne_top
  let : q.IsMaximal := hq
  obtain ⟨F, C⟩ := hboundary.curve_center_chart_at_closed_point hd I hI q (hp.trans hpq)
  obtain ⟨C⟩ := C
  exact ⟨F, ⟨C.generalization hpq⟩⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
