import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterSmoothness
import OAI.AlgebraicGeometry.Resolution.Blowups.Smooth.AlgebraReduced

/-! # Center Divided Membership -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Common boundary-center charts force each divided boundary equation into the actual center ideal. -/

universe u v

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.divided_mem_radical
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    (I : Ideal R) {ι : Type v} {w : ι → R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (j : ι) (hj : j ∈ F) : w j ∈ I.radical := by
  rw [Ideal.radical_eq_sInf]
  apply Submodule.mem_sInf.mpr
  intro P hP
  change Ideal R at P
  obtain ⟨hIP, hprime⟩ := hP
  let : P.IsPrime := hprime
  obtain ⟨C⟩ := h ⟨P, hprime⟩ hIP
  have hw : C.chart.map (w j) ∈ I.map C.chart.map.toRingHom := by
    rw [C.center_eq]
    exact C.chart.model.coordinateCenter_boundary_mem C.coordinates F C.divided_iff j hj
  have he := congrArg PrimeSpectrum.asIdeal C.chart.point_over
  change C.chart.point.asIdeal.comap C.chart.map.toRingHom = P at he
  have hle : I.map C.chart.map.toRingHom ≤ C.chart.point.asIdeal := by
    apply Ideal.map_le_iff_le_comap.mpr
    rw [he]
    exact hIP
  have hm : w j ∈ C.chart.point.asIdeal.comap C.chart.map.toRingHom := hle hw
  rwa [he] at hm

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.divided_mem
    {k : Type u} [Field k] [IsAlgClosed k] {R : CommRingCat.{u}} [Algebra k R]
    (I : Ideal R) {ι : Type v} {w : ι → R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (j : ι) (hj : j ∈ F) : w j ∈ I := by
  let : Algebra.Smooth k (R ⧸ I) := h.smooth I
  have hr : I.radical = I :=
    ((Ideal.isRadical_iff_quotient_reduced I).mpr (Blowups.Smooth.AlgebraReduced.Construction.smooth_algebra_isReduced k)).radical
  rw [← hr]
  exact h.divided_mem_radical I j hj

end

end OAI.AlgebraicGeometry.Resolution.Blowups
