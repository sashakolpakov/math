import OAI.AlgebraicGeometry.Resolution.Blowups.UnitDenominatorBoundaryModel
import OAI.AlgebraicGeometry.Resolution.Blowups.Blowup.ChartOpenBaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.RefinementHelpers

/-! # Outside Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OutsideCenter.Construction

noncomputable section

/-! Preserve explicit boundary models at every blowup point outside the center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

theorem blowupChart_denominator_not_mem_of_outside {R : Type u} [CommRing R]
    (I : Ideal R) (a : I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (hp : ¬ I ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal) :
    a.val ∉ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal := by
  intro ha
  apply hp
  intro z hz
  change Blowup.Charts.Construction.blowupChartConstants I a z ∈ p.asIdeal
  rw [← ExceptionalIdeal.Construction.blowupChartConstants_mul_ratio I a ⟨z, hz⟩]
  exact p.asIdeal.mul_mem_right _ ha

variable (k : Type u) [CommRing k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

/-- Outside the center, any existing étale boundary model pulls back to
an actual open neighborhood of the blowup point. The new exceptional
equation is a unit there, and every old equation keeps its label. -/
theorem exists_boundary_blowup_open_chart_outside_center
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (I : Ideal R) (a : I) (hw : ∀ j, w j ∈ I)
    (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (hp : ¬ I ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw) p) := by
  let A := Localization.Away a.val
  let f : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    IsOpenImmersion.of_isLocalization a.val
  have het : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)) := inferInstance
  have hf : f.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp het
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a.val
    (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)
    (blowupChart_denominator_not_mem_of_outside I a p hp)
  obtain ⟨Q, hQ, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a f.toRingHom hf p q hq
  let a' : I.map f.toRingHom := ⟨f a.val, Ideal.mem_map_of_mem _ a.property⟩
  have ha' : IsUnit a'.val := IsLocalization.Away.algebraMap_isUnit a.val
  let N := UnitDenominatorBoundaryModel.Construction.unitDenominatorBoundaryModel (M.baseChange f hf) (I.map f.toRingHom) a' ha'
    (fun j => Ideal.mem_map_of_mem f.toRingHom (hw j))
  refine ⟨{ carrier := .of (Blowup.Charts.Construction.blowupChart (I.map f.toRingHom) a')
            algebra := Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra k (I.map f.toRingHom) a'
            map := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a f
            isOpenImmersion := Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion I a f.toRingHom
            point := Q
            point_over := hQ
            model := ?_ }⟩
  have he : (fun j => Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a f
      (WithExceptional.Construction.blowupBoundaryWithExceptional I a w hw j)) =
      WithExceptional.Construction.blowupBoundaryWithExceptional (I.map f.toRingHom) a' (fun j => f (w j))
        (fun j => Ideal.mem_map_of_mem f.toRingHom (hw j)) := by
    funext j
    exact WithExceptional.Construction.blowupBoundaryWithExceptional_map I a w hw f.toRingHom j
  rw [he]
  exact N

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OutsideCenter.Construction
