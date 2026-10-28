import OAI.AlgebraicGeometry.Resolution.Blowups.FramedIdealBoundaryPreservation
import OAI.AlgebraicGeometry.Resolution.Blowups.MappedDualFrame
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OpenChartComposition

/-! # Local Boundary Blowup Preservation -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryBlowupPreservation.Construction

noncomputable section

/-! Start the boundary-preservation theorem from an actual local source model. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (k : Type u) [Field k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- A pointed source boundary chart suffices. Its actual base change to
the arbitrary blowup chart retains the original point; a further open
then gives the new and old boundary equations in distinct coordinates. -/
theorem exists_boundary_blowup_open_chart_of_local_model
    (R : CommRingCat.{u}) [Algebra k R] [Algebra.Smooth k R] (I : Ideal R)
    {ι : Type u} [Fintype ι] [DecidableEq ι]
    (g : ι → R) (D : ι → Derivation k R R)
    (hD : ∀ i j, D i (g j) = if i = j then 1 else 0)
    (hgen : Ideal.span (Set.range g) = I)
    {θ : Type v} [Fintype θ] (w : θ → R) (hw : ∀ j, w j ∈ I)
    (a : I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (C : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) p) := by
  have het : Etale (Spec.map (CommRingCat.ofHom C.map.toRingHom)) := inferInstance
  have hf : C.map.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  let : Algebra.Smooth k C.carrier := Blowups.Etale.RefinementHelpers.Construction.smooth_target_of_etale_algHom k C.map hf
  let g' : ι → C.carrier := fun j => C.map (g j)
  let D' : ι → Derivation k C.carrier C.carrier := fun j =>
    Blowups.Etale.DerivationHom.Construction.extendEtaleRingDerivationHom k C.map.toRingHom hf C.map.commutes (D j)
  have hD' : ∀ i j, D' i (g' j) = if i = j then 1 else 0 :=
    MappedDualFrame.Construction.etale_mapped_dual_frame k C.map hf g D hD
  have hgen' : Ideal.span (Set.range g') = I.map C.map.toRingHom := by
    calc
      Ideal.span (Set.range g') = (Ideal.span (Set.range g)).map C.map.toRingHom := by
        rw [Ideal.map_span, ← Set.range_comp]
        rfl
      _ = I.map C.map.toRingHom := congrArg (Ideal.map C.map.toRingHom) hgen
  obtain ⟨Q, hQ, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a C.map.toRingHom hf p C.point C.point_over
  let a' : I.map C.map.toRingHom := ⟨C.map a.val, Ideal.mem_map_of_mem _ a.property⟩
  obtain ⟨B⟩ := FramedIdealBoundaryPreservation.Construction.exists_framed_ideal_boundary_blowup_open_chart k C.carrier
    (I.map C.map.toRingHom) g' D' hD' hgen' (fun j => C.map (w j)) C.model
    (fun j => Ideal.mem_map_of_mem _ (hw j)) a' Q
  let f := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a C.map
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion I a C.map.toRingHom
  exact ⟨B.comp f (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw)
    (Boundary.WithExceptional.Construction.blowupBoundaryWithExceptional_map I a w hw C.map.toRingHom) p hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryBlowupPreservation.Construction
