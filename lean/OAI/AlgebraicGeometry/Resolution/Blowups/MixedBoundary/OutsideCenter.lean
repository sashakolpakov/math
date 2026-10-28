import OAI.AlgebraicGeometry.Resolution.Blowups.Mixed.UnitDenominatorBoundary
import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.BaseChange
import OAI.AlgebraicGeometry.Resolution.Blowups.Boundary.OutsideCenter

/-! # Outside Center -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.OutsideCenter.Construction

noncomputable section

/-! Full mixed boundary preservation outside the actual center. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable (k : Type u) [CommRing k]

attribute [local instance] Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra

theorem exists_mixed_boundary_open_chart_outside_center
    (R : CommRingCat.{u}) [Algebra k R] {ι : Type v} (w : ι → R)
    (M : Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (I : Ideal R) (a : I)
    (F : Finset ι) (hw : ∀ j ∈ F, w j ∈ I) (p : PrimeSpectrum (Blowup.Charts.Construction.blowupChart I a))
    (hp : ¬ I ≤ (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p).asIdeal) :
    Nonempty (Blowups.Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k (.of (Blowup.Charts.Construction.blowupChart I a))
      (Equations.Construction.blowupMixedBoundaryFamily I a F w hw) p) := by
  let A := Localization.Away a.val
  let f : R →ₐ[k] A := IsScalarTower.toAlgHom k R A
  let : IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom)) :=
    IsOpenImmersion.of_isLocalization a.val
  have hf : f.toRingHom.Etale := (HasRingHomProperty.Spec_iff (P := @Etale)).mp
    (inferInstance : Etale (Spec.map (CommRingCat.ofHom f.toRingHom)))
  obtain ⟨q, hq⟩ := Blowups.Etale.RefinementHelpers.Construction.exists_localization_away_prime a.val
    (PrimeSpectrum.comap (Blowup.Charts.Construction.blowupChartConstants I a) p)
    (Boundary.OutsideCenter.Construction.blowupChart_denominator_not_mem_of_outside I a p hp)
  obtain ⟨Q, hQ, _⟩ := Blowup.ChartOpenBaseChange.Construction.exists_blowupChartMap_prime I a f.toRingHom hf p q hq
  let a' : I.map f.toRingHom := ⟨f a.val, Ideal.mem_map_of_mem _ a.property⟩
  have ha' : IsUnit a'.val := IsLocalization.Away.algebraMap_isUnit a.val
  let N := Mixed.UnitDenominatorBoundary.Construction.mixedUnitDenominatorBoundaryModel (M.baseChange f hf) (I.map f.toRingHom) a' ha' F
    (fun j hj => Ideal.mem_map_of_mem f.toRingHom (hw j hj))
  refine ⟨{ carrier := .of (Blowup.Charts.Construction.blowupChart (I.map f.toRingHom) a')
            algebra := Relative.DifferentialBlowup.Construction.blowupRelativeBaseAlgebra k (I.map f.toRingHom) a'
            map := Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a f
            isOpenImmersion := Blowup.ChartOpenBaseChange.Construction.blowupChartMap_isOpenImmersion I a f.toRingHom
            point := Q
            point_over := hQ
            model := ?_ }⟩
  have he : (fun j => Blowup.ChartOpenBaseChange.Construction.blowupChartMapAlgHom k I a f (Equations.Construction.blowupMixedBoundaryFamily I a F w hw j)) =
      Equations.Construction.blowupMixedBoundaryFamily (I.map f.toRingHom) a' F (fun j => f (w j))
        (fun j hj => Ideal.mem_map_of_mem f.toRingHom (hw j hj)) := by
    funext j
    exact BaseChange.Construction.blowupMixedBoundaryFamily_map I a F w hw f.toRingHom j
  rw [he]
  exact N

end

end OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.OutsideCenter.Construction
