import OAI.AlgebraicGeometry.Resolution.Blowups.Global.MixedCenterCoordinateChart
import OAI.AlgebraicGeometry.Resolution.Blowups.SupportedBoundaryCenterExtension

/-! # Mixed Center Support Charts -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Pointed common-center charts need only be supplied along the actual center support. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofCenterCharts
    {X : Scheme} (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (I : X.IdealSheafData)
    {β : Type} (D : β → X.IdealSheafData) {L : List (Finset β)}
    (A : MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D L)
    (h : ∀ x : X, x ∈ I.support → ∃ C : MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart f I D,
      ∃ p : PrimeSpectrum C.ring, C.map p = x) : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas f I D := by
  apply CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas.ofPointedCharts f I D
  intro x
  by_cases hx : x ∈ I.support
  · exact h x hx
  · let O : X.Opens := I.support.compl
    let y : O := ⟨x, hx⟩
    let B : CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas (O.ι ≫ f) (I.comap O.ι) (fun l => (D l).comap O.ι) := by
      rw [ResidualNeighborhood.Construction.idealSheaf_comap_supportComplement_eq_top]
      exact (A.comapOpen f O.ι).unitCenter
    obtain ⟨i, p, hp⟩ := MonomialBoundaryAtlas.Construction.exists_point_on_chosen_affine_spec B.opens B.cover y
    let C := (MixedCenterCoordinateChart.Construction.GlobalMixedCenterOpenChart.ofAtlas B i).comp f I D O.ι
    refine ⟨C, p, ?_⟩
    change O.ι ((B.opens i).2.fromSpec p) = x
    exact congrArg O.ι hp

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
