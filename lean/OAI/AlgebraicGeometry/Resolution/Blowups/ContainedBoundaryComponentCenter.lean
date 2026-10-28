import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.CenterEtaleBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.ComponentTransverseDerivation
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalContainedHypersurfaceCenter
import OAI.AlgebraicGeometry.Resolution.Blowups.ContainedHypersurfaceBoundaryBlowup

/-! # Contained Boundary Component Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A contained component of the full local boundary can be added to every compatible center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.adjoin_boundary_component
    {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι] {w : ι → R} {I : Ideal R} {F : Finset ι}
    (hcenter : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (z : R) (hz : z ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R
      (fun j : Option ι => match j with | none => z | some j => w j)) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I
      (fun j : Option ι => match j with | none => z | some j => w j)
      (insert none (F.image some)) := by
  classical
  intro p hp
  let v : Option ι → R := fun j => match j with | none => z | some j => w j
  obtain ⟨B⟩ := hboundary p
  have hf : B.map.toRingHom.Etale :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp
      (inferInstance : Etale (Spec.map (CommRingCat.ofHom B.map.toRingHom)))
  have hpoint : B.point.asIdeal.comap B.map.toRingHom = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal B.point_over
  have hIp : I.map B.map.toRingHom ≤ B.point.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hpoint]
    exact hp
  have hzmap : B.map z ∈ I.map B.map.toRingHom := Ideal.mem_map_of_mem B.map.toRingHom hz
  obtain ⟨C⟩ := hcenter.etale_baseChange B.map hf B.point hIp
  let e : ι ↪ Option ι := ⟨some, Option.some_injective ι⟩
  have hne (j : ι) : (none : Option ι) ≠ e j := by
    intro h
    change (none : Option ι) = some j at h
    cases h
  obtain ⟨E, hE, hEz⟩ := B.model.exists_component_transverse_derivation none e
    hne B.point (hIp hzmap)
  have hE' : E ∈ Relative.LogarithmicIdeal.Construction.relativeLogarithmicDerivations k (fun j => B.map (w j)) := by
    intro j
    exact hE j
  obtain ⟨O⟩ := C.adjoin_contained_hypersurface hIp (B.map z) hzmap E hE' hEz
  have O' : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k B.carrier (I.map B.map.toRingHom)
      (fun j => B.map (v j)) (insert none (F.image some)) B.point := by
    convert O using 1
    funext j
    cases j <;> rfl
  exact ⟨MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.comp (R := R) (S := B.carrier)
    I v (insert none (F.image some)) B.map O' p B.point_over⟩

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem ContainedBoundaryComponentCenter.Construction.contained_boundary_component_preserves_full_blowup_boundary
    {k : Type u} [Field k] (R : CommRingCat.{u}) [Algebra k R]
    {ι : Type v} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) (z : R) (hz : z ∈ I) (w : ι → R) (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I)
    (hboundary : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R
      (fun j : Option ι => match j with | none => z | some j => w j))
    (hcenter : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (a : I) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k (.of (Blowup.Charts.Construction.blowupChart I a))
      (MixedBoundary.Equations.Construction.blowupMixedBoundaryFamily I a (insert none (F.image some))
        (fun j : Option ι => match j with | none => z | some j => w j)
        (ContainedHypersurfaceBoundaryBlowup.Construction.adjoined_boundary_center_mem I z hz w F hw)) := by
  exact MixedBoundary.AdmissiblePreservation.Construction.hasEtaleBoundaryCharts_mixed_admissible_blowup R I
    (fun j : Option ι => match j with | none => z | some j => w j)
    (insert none (F.image some)) (ContainedHypersurfaceBoundaryBlowup.Construction.adjoined_boundary_center_mem I z hz w F hw)
    hboundary (hcenter.adjoin_boundary_component z hz hboundary) a

end

end OAI.AlgebraicGeometry.Resolution.Blowups
