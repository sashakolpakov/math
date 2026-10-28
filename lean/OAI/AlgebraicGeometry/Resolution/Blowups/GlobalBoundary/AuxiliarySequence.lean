import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.Auxiliary
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.ControlBoundaryEndpoint
import OAI.AlgebraicGeometry.Resolution.Blowups.Global.OrderBoundPreservation

/-! # Auxiliary Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual global auxiliary sequences clear the transformed old boundary at the original marked control. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.auxiliary_terminalIdeal
    {m : ℕ} (hm : 0 < m) {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {K : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence m X f K) (J L : X.IdealSheafData)
    (hK : K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) :
    T.terminalIdeal = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (T.transformIdeal J m) (T.transformIdeal L 1) m := by
  revert hK J L
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _ J L hK
      exact hK
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg J L hK
      let : Smooth g := hg
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      obtain ⟨hJ, hL⟩ := (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_smooth_center_iff g I J L m hm).mp (hK ▸ hp)
      apply ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI 1)
      rw [hK, GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_transform I J L hI m hJ hL]

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.auxiliary_terminal_clearance
    {m : ℕ} (hm : 0 < m) {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {K : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence m X f K) (J L : X.IdealSheafData)
    (hK : K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) (T.transformIdeal J m) (m - 1) ⊔ T.transformIdeal L 1 = ⊤ := by
  have ht := T.terminal_differential_ideal
  rw [T.auxiliary_terminalIdeal hm J L hK] at ht
  exact (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_terminal_iff (T.toBase ≫ f) _ _ m hm).mp ht

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.auxiliary_retains_residual_bound
    {m : ℕ} (hm : 0 < m) {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {K : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence m X f K) (J L : X.IdealSheafData)
    (hK : K = GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J L m)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) (T.transformIdeal J m) m = ⊤ := by
  revert hK hbound J L
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs K ht =>
      intro _ J L _ hb
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (𝟙 Y ≫ g) J m = ⊤
      exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr (𝟙 Y ≫ g) g (Category.id_comp g) J m).trans hb
  | @blowup Y hY hN g K I hI hb hp hs hbl tail ih =>
      intro hg J L hK hbound
      let : Smooth g := hg
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      obtain ⟨hJ, hL⟩ := (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_smooth_center_iff g I J L m hm).mp (hK ▸ hp)
      have he : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I K hI m =
          GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI 1) m := by
        rw [hK, GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal_transform I J L hI m hJ hL]
      have h := ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI 1) he
        (Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound g I J hI m hJ hbound)
      let : Smooth ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g) := by
        rw [Category.assoc]
        exact inferInstanceAs (Smooth (tail.toBase ≫ (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g)))
      change Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf ((tail.toBase ≫ GlobalBlowup.Data.Construction.globalBlowupToBase I hI) ≫ g)
        (tail.transformIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m) m = ⊤
      exact (DifferentialUnitGluing.Construction.smoothDifferentialIdealSheaf_structure_congr _ _ (Category.assoc _ _ _)
        (tail.transformIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) m) m).trans h

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.auxiliary_clears_original_boundary_label
    {m : ℕ} (hm : 0 < m) {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f]
    {β : Type} (D : β → X.IdealSheafData) (j : β) (J : X.IdealSheafData)
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence m X f (GlobalBoundary.Auxiliary.Construction.globalBoundaryAuxiliaryIdeal J (D j) m)) :
    Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf (T.toBase ≫ f) (T.transformIdeal J m) (m - 1) ⊔
      T.endpointBoundary D (T.initialLabelEmbedding β j) = ⊤ := by
  rw [T.endpointBoundary_initialLabel]
  exact T.auxiliary_terminal_clearance hm J (D j) rfl

end

end OAI.AlgebraicGeometry.Resolution.Blowups
