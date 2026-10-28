import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts

/-! # Mixed Center Chart -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! A displayed common coordinate model witnesses a compatible center at every point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def Etale.BoundaryModel.Construction.EtaleBoundaryModel.mixedCenterChart {k : Type u} [Field k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v} {w : ι → R}
    (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s) (p : PrimeSpectrum R) :
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) w F p := by
  let B : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p :=
    { carrier := R
      algebra := inferInstance
      map := AlgHom.id k R
      isOpenImmersion := by
        change IsOpenImmersion (Spec.map (𝟙 R))
        rw [Spec.map_id]
        infer_instance
      point := p
      point_over := PrimeSpectrum.ext rfl
      model := M }
  exact { chart := B
          coordinates := C
          center_eq := Ideal.map_id _
          divided_iff := hF }

theorem Etale.BoundaryModel.Construction.EtaleBoundaryModel.hasMixedCenterCharts {k : Type u} [Field k]
    {R : CommRingCat.{u}} [Algebra k R] {ι : Type v} {w : ι → R}
    (M : Etale.BoundaryModel.Construction.EtaleBoundaryModel k R ι w) (C : Finset M.indices) (F : Finset ι)
    (hF : ∀ j, j ∈ F ↔ ∃ s ∈ C, M.coordinate j = some s) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R ((SubsetCoordinateBlowup.Construction.subsetCoordinateIdeal C).map M.map) w F :=
  fun p _ => ⟨M.mixedCenterChart C F hF p⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
