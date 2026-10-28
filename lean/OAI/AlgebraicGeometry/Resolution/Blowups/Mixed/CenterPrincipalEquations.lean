import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.CenterCharts
import OAI.AlgebraicGeometry.Resolution.Blowups.BoundaryModel.PrincipalEquations
import OAI.AlgebraicGeometry.Resolution.Blowups.LocalBoundaryProperty

/-! # Center Principal Equations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Common center charts depend on the labelled principal ideals, not their chosen generators. -/

universe u v

variable {k : Type u} [Field k] {R : CommRingCat.{u}} [Algebra k R]
  {β : Type v} {w : β → R} {p : PrimeSpectrum R}

def Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart.replacePrincipalEquations (C : Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R w p)
    (v : β → R) (hv : ∀ j, Ideal.span {w j} = Ideal.span {v j}) :
    Etale.BoundaryModel.Construction.EtaleBoundaryOpenChart k R v p where
  carrier := C.carrier
  algebra := C.algebra
  map := C.map
  isOpenImmersion := C.isOpenImmersion
  point := C.point
  point_over := C.point_over
  model := C.model.replacePrincipalEquations (fun j => C.map (v j)) (by
    intro j
    have h := congrArg (fun I : Ideal R => I.map C.map.toRingHom) (hv j)
    rw [Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton] at h
    exact h)

theorem LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts.replacePrincipalEquations (h : LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R w)
    (v : β → R) (hv : ∀ j, Ideal.span {w j} = Ideal.span {v j}) :
    LocalBoundaryProperty.Construction.HasEtaleBoundaryCharts k R v := by
  intro p
  obtain ⟨C⟩ := h p
  exact ⟨C.replacePrincipalEquations v hv⟩

def MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart.replacePrincipalEquations
    {I : Ideal R} {F : Finset β} (C : MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I w F p)
    (v : β → R) (hv : ∀ j, Ideal.span {w j} = Ideal.span {v j}) :
    MixedBoundary.CenterCharts.Construction.MixedBoundaryCoordinateCenterOpenChart k R I v F p where
  chart := C.chart.replacePrincipalEquations v hv
  coordinates := C.coordinates
  center_eq := C.center_eq
  divided_iff := C.divided_iff

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.replacePrincipalEquations
    {I : Ideal R} {F : Finset β} (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F)
    (v : β → R) (hv : ∀ j, Ideal.span {w j} = Ideal.span {v j}) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I v F := by
  intro p hp
  obtain ⟨C⟩ := h p hp
  exact ⟨C.replacePrincipalEquations v hv⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
