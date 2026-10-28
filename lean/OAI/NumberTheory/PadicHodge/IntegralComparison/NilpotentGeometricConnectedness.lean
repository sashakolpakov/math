import OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentFiberAmpleness
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-! # Nilpotent Geometric Connectedness -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentGeometricConnectedness

noncomputable section

/-! Geometric connectedness lifts through an actual nilpotent
coefficient reduction, because every field-valued base map factors
through that reduction. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {R k : Type u} [CommRing R] [CommRing k]
  (ρ : R →+* k) (hρ : Function.Surjective ρ)
  (hker : ∀ a ∈ RingHom.ker ρ, IsNilpotent a)
  {X Y : Scheme.{u}} (f : X ⟶ Spec (.of R)) (g : Y ⟶ Spec (.of k))
  (i : Y ⟶ X) (hp : IsPullback i g f (Spec.map (CommRingCat.ofHom ρ)))
  [GeometricallyConnected g]

include hρ hker hp in
theorem connected : GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ b => ?_⟩
  obtain ⟨c, hc⟩ := NilpotentFiberAmpleness.field_factor ρ hρ hker b
  have hs := (IsPullback.of_hasPullback g c).paste_horiz hp
  rw [hc] at hs
  let : ConnectedSpace ↥(pullback g c) :=
    GeometricallyConnected.connectedSpace_of_subsingleton (pullback.snd g c)
  exact hs.isoPullback.hom.homeomorph.connectedSpace_iff.mp inferInstance

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.NilpotentGeometricConnectedness
