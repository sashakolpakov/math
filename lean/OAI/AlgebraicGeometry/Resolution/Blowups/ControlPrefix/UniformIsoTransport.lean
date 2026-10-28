import OAI.AlgebraicGeometry.Resolution.Blowups.IncidenceTraceOpenDescent

/-! # Uniform Iso Transport -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Transport a recorded prefix through an isomorphism while retaining its exact trace and actual endpoint comparison. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_uniform_iso_transport
    {b : ℕ} {V W : Scheme} {g : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {L : V.IdealSheafData} {M : W.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V g L W k M)
    {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f] (J : X.IdealSheafData) (hJ : J ≠ ⊥)
    (e : V ≅ X) (hg : e.hom ≫ f = g) (hL : J.comap e.hom = L)
    {β : Type} [Fintype β] (D : β → X.IdealSheafData)
    (A : Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas f D [Finset.univ]) (T : Boundary.IncidenceTrace.Construction.BoundaryIncidenceTrace β)
    (hP : P.HasIncidenceTrace β (fun l => (D l).comap e.hom) T) :
    ∃ (Y : Scheme) (h : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (K : Y.IdealSheafData) (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y h K)
      (r : W ⟶ Y), Q.HasIncidenceTrace β D T ∧ Q.EtaleComparison P e.hom r ∧ IsIso r := by
  have hcover : ((Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (b - 1)).support : Set X) ⊆ Set.range e.hom := by
    intro x _
    refine ⟨e.inv x, ?_⟩
    change (e.inv ≫ e.hom) x = x
    rw [e.inv_hom_id]
    rfl
  obtain ⟨Y, h, K, Q, r, _, hc, _, _⟩ := P.exists_uniform_extension_from_order_neighborhood X f J hJ
    e.hom hg hL hcover β D A (hP.uniformBoundaryCompatible P _ T)
  have hQ := Q.hasIncidenceTrace_of_order_neighborhood P e.hom r hc hcover β D A T hP
  have hpb := (hc.endpoint_pullback Q P e.hom r).2.1
  refine ⟨Y, h, K, Q, r, hQ, hc, ?_⟩
  rw [← hpb.isoPullback_hom_fst]
  infer_instance

end

end OAI.AlgebraicGeometry.Resolution.Blowups
