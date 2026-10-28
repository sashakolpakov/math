import OAI.AlgebraicGeometry.Resolution.Blowups.NamedContainedCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterComposition

/-! # Local Contained Hypersurface Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Adjoin a contained transverse hypersurface to an actual local common-coordinate center chart. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.adjoin_contained_hypersurface
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {w : ι → R} {I : Ideal R} {F : Finset ι}
    {p : PrimeSpectrum R} (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p)
    (hIp : I ≤ p.asIdeal) (z : R) (hz : z ∈ I)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z ∉ p.asIdeal) :
    Nonempty (MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) p) := by
  classical
  have hf : C.chart.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.map (CommRingCat.ofHom C.chart.map.toRingHom)))
  let : Algebra R C.chart.carrier := C.chart.map.toRingHom.toAlgebra
  let : IsScalarTower k R C.chart.carrier :=
    IsScalarTower.of_algebraMap_eq (fun c => (C.chart.map.commutes c).symm)
  let : Algebra.Etale R C.chart.carrier := RingHom.etale_algebraMap.mp hf
  have hpoint : C.chart.point.asIdeal.comap C.chart.map.toRingHom = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal C.chart.point_over
  have hcenter : I.map C.chart.map.toRingHom ≤ C.chart.point.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hpoint]
    exact hIp
  have hzmap : C.chart.map z ∈ I.map C.chart.map.toRingHom :=
    Ideal.mem_map_of_mem C.chart.map.toRingHom hz
  let D := Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := C.chart.carrier) E
  have hD : D ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => C.chart.map (w j)) :=
    Relative.LogarithmicBoundary.Construction.extendEtaleRingDerivation_relative_logarithmic (S := C.chart.carrier) k w ⟨E, hE⟩
  have hDz : D (C.chart.map z) ∉ C.chart.point.asIdeal := by
    change Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation (S := C.chart.carrier) E
      (algebraMap R C.chart.carrier z) ∉ C.chart.point.asIdeal
    rw [Blowups.Etale.Derivation.Construction.extendEtaleRingDerivation_algebraMap]
    intro h
    apply hEz
    have h' : E z ∈ C.chart.point.asIdeal.comap C.chart.map.toRingHom := h
    rwa [hpoint] at h'
  obtain ⟨O⟩ := Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel.named_contained_hypersurface_center_chart
    (R := C.chart.carrier) C.chart.model (I.map C.chart.map.toRingHom) C.coordinates C.center_eq
    F C.divided_iff C.chart.point hcenter (C.chart.map z) hzmap D hD hDz
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  have O' : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k C.chart.carrier (I.map C.chart.map.toRingHom)
      (fun j => C.chart.map (v j)) (insert none (F.image some)) C.chart.point := by
    convert O using 1
    funext j
    cases j <;> rfl
  exact ⟨MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.comp (R := R) (S := C.chart.carrier)
    I v (insert none (F.image some)) C.chart.map O' p C.chart.point_over⟩

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.adjoin_contained_hypersurface
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {w : ι → R} {I : Ideal R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (z : R) (hz : z ∈ I)
    (E : Derivation k R R) (hE : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k w) (hEz : E z = 1) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) := by
  intro p hp
  obtain ⟨C⟩ := h p hp
  apply C.adjoin_contained_hypersurface hp z hz E hE
  rw [hEz]
  exact p.isPrime.one_notMem

end

end OAI.AlgebraicGeometry.Resolution.Blowups
