import OAI.AlgebraicGeometry.Resolution.Blowups.ControlPrefix.CenterComparison
import OAI.AlgebraicGeometry.Resolution.Blowups.Etale.PullbackCenter

/-! # Etale Pullback Existence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Construct the actual pullback of every recorded permissible prefix along an étale morphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Smooth.ControlPrefix.Construction.SmoothControlPrefix.exists_etale_pullback
    {b : ℕ} {X Y : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {g : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase}
    {J : X.IdealSheafData} {K : Y.IdealSheafData} (P : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b X f J Y g K) :
    ∀ (V : Scheme) [IsIntegral V] [IsLocallyNoetherian V]
      (h : V ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (L : V.IdealSheafData) (q : V ⟶ X) [Etale q],
      q ≫ f = h → J.comap q = L →
      ∃ (W : Scheme) (k : W ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (M : W.IdealSheafData)
        (Q : Blowups.Smooth.ControlPrefix.Construction.SmoothControlPrefix b V h L W k M) (r : W ⟶ Y), P.EtaleComparison Q q r := by
  induction P with
  | stop =>
      intro V _ _ h L q _ hstructure hJ
      have hh : Smooth h := hstructure ▸ inferInstanceAs (Smooth (q ≫ _))
      let : Smooth h := hh
      exact ⟨V, h, L, .stop, q, inferInstance, hstructure, hJ, rfl⟩
  | @blowup X hX hNX f J I hI hb hp hs hbl Y g K tail ih =>
      intro V _ _ h L q _ hstructure hJ
      let C := I.comap q
      have hC : C ≠ ⊥ := Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_nonempty_etale_ne_bot q I hI
      let q' := GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo q I C rfl hI hC
      let : Etale q' := GlobalBlowup.EtaleMap.Construction.globalBlowupMapTo_etale q I C rfl hI hC
      have hover : q' ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) = GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h := by
        rw [← Category.assoc, GlobalBlowup.SpecifiedMap.Construction.globalBlowupMapTo_over, Category.assoc, hstructure]
      have hL' : (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI b).comap q' =
          GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b := by
        rw [GlobalBlowup.EtaleBoundary.Construction.globalBlowupMapTo_controlledIdeal_etale q I J C rfl hI hC b, hJ]
      have hpC : L ≤ C ^ b := by
        rw [← hJ, ← IdealSheaf.ProductPullback.Construction.idealSheaf_comap_pow]
        exact Scheme.IdealSheafData.comap_mono q hp
      let : Smooth (I.subschemeι ≫ f) := hs
      have hsC : Smooth (C.subschemeι ≫ h) := by
        rw [← hstructure]
        exact Blowups.Etale.PullbackCenter.Construction.idealSheaf_comap_etale_smooth_center f q I
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f) := hbl
      have hblC : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h) := hover ▸ inferInstanceAs
        (Smooth (q' ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)))
      obtain ⟨W, k, M, Q, r, hQ⟩ := ih (GlobalBlowup.Data.Construction.globalBlowup C hC) (GlobalBlowup.Data.Construction.globalBlowupToBase C hC ≫ h)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal C L hC b) q' hover hL'
      exact ⟨W, k, M, .blowup C hC hb hpC hsC hblC Q, r, inferInstance, hstructure, hJ, rfl, hQ⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
