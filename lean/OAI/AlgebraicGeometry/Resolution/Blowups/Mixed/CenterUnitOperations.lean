import OAI.AlgebraicGeometry.Resolution.Blowups.MixedBoundary.PartialLabelTransform

/-! # Center Unit Operations -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Common center coordinates are unchanged by unit equations and by an extra invertible boundary label. -/

universe u v

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.mulUnits
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {I : Ideal R} {w : ι → R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (u : ι → R) (hu : ∀ j, IsUnit (u j)) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I (fun j => u j * w j) F := by
  apply h.pullbackLabels (fun j => some j)
    (fun i j s hi hj => Option.some.inj (hi.trans hj.symm)) (fun j => u j * w j) u hu
    (fun _ => rfl) F
  intro j
  simp only [Option.some.injEq]
  constructor
  · intro hj
    exact ⟨j, hj, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact hs

theorem MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts.adjoinUnit
    {k : Type u} [CommRing k] {R : CommRingCat.{u}} [Algebra k R]
    {ι : Type v} {I : Ideal R} {w : ι → R} {F : Finset ι}
    (h : MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I w F) (c : R) (hc : IsUnit c) :
    MixedBoundary.CenterCharts.Construction.HasMixedBoundaryCenterCharts k R I
      (fun j : Option ι => match j with | none => c | some i => w i)
      (F.map Function.Embedding.some) := by
  classical
  apply h.pullbackLabels id (fun i j s hi hj => hi.trans hj.symm)
    (fun j => match j with | none => c | some i => w i)
    (fun j => match j with | none => c | some _ => 1)
  · intro j
    cases j with
    | none => exact hc
    | some _ => exact isUnit_one
  · intro j
    cases j <;> simp
  · intro j
    cases j <;> simp

end

end OAI.AlgebraicGeometry.Resolution.Blowups
