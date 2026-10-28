import OAI.AlgebraicGeometry.Resolution.Blowups.Surface.ResidualProgram
import OAI.AlgebraicGeometry.Resolution.Blowups.ResidualNeighborhoodEtalePullback

/-! # Residual Program Naturality -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Surface

noncomputable section

/-! Complete residual programs with one schedule compare at every blowup, including ambient extensions from residual neighborhoods. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem ResidualProgram.Construction.SurfaceResidualProgram.exists_etaleComparison {b m : ℕ} {β : Type} [Fintype β] [DecidableEq β]
    {a : β → ℕ} {schedule : ResidualSchedule.Construction.SurfaceResidualSchedule b m β a}
    {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J I : X.IdealSheafData} {K : Y.IdealSheafData} {D : β → X.IdealSheafData}
    {P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f I Y g K}
    (H : ResidualProgram.Construction.SurfaceResidualProgram b schedule X f J I D Y g K P) :
    ∀ [Smooth f] {V W : Scheme} {h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth h] {k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
      {J₁ I₁ : V.IdealSheafData} {M : W.IdealSheafData} {E : β → V.IdealSheafData}
      {Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h I₁ W k M},
      ResidualProgram.Construction.SurfaceResidualProgram b schedule V h J₁ I₁ E W k M Q →
      ∀ (q : V ⟶ X) [Etale q], q ≫ f = h → J.comap q = J₁ → I.comap q = I₁ →
      (∀ l, (D l).comap q = E l) → ∃ r : W ⟶ Y, P.EtaleComparison Q q r := by
  induction H with
  | monomial a S H =>
      intro _ V W h _ k J₁ I₁ M E Q H' q _ hover hJ hI hD
      cases H' with
      | monomial a S H' => exact H.exists_etaleComparison H' q hover hI hD
  | higher a hle S schedule A order P same R tail ih =>
      intro _ V W h _ k J₁ I₁ M E Q H' q _ hover hJ hI hD
      cases H' with
      | higher a hle S schedule A' order' P' same' R' tail' =>
          let _ := A.endpoint_smooth
          let _ := A'.endpoint_smooth
          obtain ⟨u, hu⟩ := order.exists_etaleComparison order' q hover hJ hD
          let : Etale u := (hu.endpoint_pullback A A' q u).1
          have hp := same.etaleComparison same' q u hu hI
          have hg := hu.endpoint_structure A A' q u
          have hJ' := (hu.endpoint_pullback A A' q u).2.2
          have hI' := (hp.endpoint_pullback P P' q u).2.2
          have hboundary := hu.boundaryAtLength A A' q u _ _ _ hD S.incidenceTrace.length
            (order.hasIncidenceTrace.stepCount A _ _) (order'.hasIncidenceTrace.stepCount A' _ _)
          obtain ⟨r, hr⟩ := ih tail' u hg hJ' hI' (fun l => congrFun hboundary l)
          exact ⟨r, hp.append P P' q u R R' r hr⟩
  | @companion m β _ _ a hlt S schedule X Y f hf g hg J I C J' I' D A order B sameB P same V₀ Z h₀ k₀ L₀ M₀ T tail R r comparison hstart hcover ih =>
      intro _ V W h _ k J₁ I₁ M E Q H' q _ hover hJ hI hD
      cases H' with
      | companion a hlt S schedule A' order' B' sameB' P' same' T' tail' R' r' comparison' hstart' hcover' =>
          have hC : (Global.CompanionIdeal.Construction.globalCompanionIdeal J (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b).comap q =
              Global.CompanionIdeal.Construction.globalCompanionIdeal J₁ (Global.MixedBoundary.Construction.boundaryMonomialSheaf E a) (m + 1) b := by
            rw [Global.CompanionIdeal.Construction.globalCompanionIdeal_comap, ResidualNeighborhoodEtalePullback.Construction.boundaryMonomialSheaf_comap, hJ]
            exact congrArg (fun D => Global.CompanionIdeal.Construction.globalCompanionIdeal J₁ (Global.MixedBoundary.Construction.boundaryMonomialSheaf D a) (m + 1) b) (funext hD)
          obtain ⟨u, hu⟩ := order.exists_etaleComparison order' q hover hC hD
          let : Etale u := (hu.endpoint_pullback A A' q u).1
          have hp := same.etaleComparison same' q u hu hI
          have hb := sameB.etaleComparison sameB' q u hu hJ
          have hg := hu.endpoint_structure A A' q u
          have hJ' := (hb.endpoint_pullback B B' q u).2.2
          have hI' := (hp.endpoint_pullback P P' q u).2.2
          have hboundary := hu.boundaryAtLength A A' q u _ _ _ hD S.incidenceTrace.length
            (order.hasIncidenceTrace.stepCount A _ _) (order'.hasIncidenceTrace.stepCount A' _ _)
          obtain ⟨v, hv, hpb⟩ := ResidualNeighborhoodEtalePullback.Construction.exists_residual_order_neighborhood_etale_pullback _ _ _ _ (m + 1) u hg hJ'
          let : Etale v := hv
          obtain ⟨w, hw⟩ := ih tail' v
            (by rw [← Category.assoc, hpb.w, Category.assoc, hg])
            (by rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, hJ'])
            (by rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, hI'])
            (by
              intro l
              rw [← Scheme.IdealSheafData.comap_comp, hpb.w, Scheme.IdealSheafData.comap_comp, congrFun hboundary l])
          have hcombined := comparison.comp R T _ r T' v w hw
          rw [hpb.w] at hcombined
          obtain ⟨s, hs⟩ := R.exists_etaleComparison_of_order_neighborhood R' u hg hI' T'
            _ (w ≫ r) r' hcombined comparison' hstart'
          exact ⟨s, hp.append P P' q u R R' s hs⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Surface
