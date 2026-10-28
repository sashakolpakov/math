import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.OrderSequenceExtension

/-! # Integral Iso Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Whole integral-center, boundary-compatible sequences transport across actual ambient isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.transport_boundary_integral_iso
    {b : ℕ} {V : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {L : V.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence b V g L) (hT : T.integralCenters)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (e : V ≅ X) (hg : e.hom ≫ f = g) (hL : J.comap e.hom = L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ])
    (hB : T.boundaryCompatible β (fun l => (D l).comap e.hom)) :
    ∃ U : Global.MonomialSequence.Construction.SmoothFixedControlSequence b X f J, U.integralCenters ∧ U.boundaryCompatible β D := by
  apply T.extend_boundary_integral_from_order_neighborhood X f J hJ e.hom hg hL _ β D A hT hB
  intro x _
  refine ⟨e.inv x, ?_⟩
  change (e.inv ≫ e.hom) x = x
  rw [e.inv_hom_id]
  rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
