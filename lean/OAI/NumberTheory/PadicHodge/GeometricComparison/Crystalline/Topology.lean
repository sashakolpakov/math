import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.Cocontinuous

/-! # Topology -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Topology

noncomputable section

/-! GeometricComparison uses IntegralComparison's actual big crystalline site. Both continuity and
cocontinuity of postcomposition are proved there from principal-open
refinements; no topology or pullback comparison is assumed here. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite

abbrev topology {p : ℕ} {B : Type} [CommRing B]
    {J : Ideal B} {δ : DividedPowers J}
    {X : Scheme} {f : X ⟶ Spec (CommRingCat.of B)} :
    GrothendieckTopology (IntegralComparison.BigCrystallineSite.Object p B J δ f) := IntegralComparison.BigCrystallineSite.Object.topology

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Crystalline.Topology
