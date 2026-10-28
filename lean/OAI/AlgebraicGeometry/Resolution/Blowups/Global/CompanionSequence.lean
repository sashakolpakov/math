import OAI.AlgebraicGeometry.Resolution.Blowups.Global.CompanionTransform
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalSurface.BoundedSequence

/-! # Companion Sequence -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Global

noncomputable section

/-! Actual global companion phases with separate residual and exceptional controls. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

inductive CompanionSequence.Construction.SmoothGlobalCompanionSequence (m b : ℕ) :
    (X : Scheme) → (X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) → X.IdealSheafData → X.IdealSheafData → Type 1
  | terminal {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {M J : X.IdealSheafData}
      (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤)
      (hdrop : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (M * J) (b - 1) ⊔ Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J (m - 1) = ⊤) :
      SmoothGlobalCompanionSequence m b X f M J
  | blowup {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]
      {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {M J : X.IdealSheafData}
      (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤)
      (I : X.IdealSheafData) (hI : I ≠ ⊥) (hM : M ≤ I ^ (b - m)) (hJ : J ≤ I ^ m)
      (hs : Smooth (I.subschemeι ≫ f)) (hbl : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f))
      (tail : SmoothGlobalCompanionSequence m b (GlobalBlowup.Data.Construction.globalBlowup I hI) (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ f)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)) :
      SmoothGlobalCompanionSequence m b X f M J

def MonomialSequence.Construction.SmoothFixedControlSequence.toCompanion
    {m b : ℕ} (hm : 0 < m) (hmb : m < b)
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {K : X.IdealSheafData}
    (T : MonomialSequence.Construction.SmoothFixedControlSequence (m * (b - m)) X f K)
    (J M : X.IdealSheafData) (hK : K = CompanionIdeal.Construction.globalCompanionIdeal J M m b)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤) : CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J := by
  revert hK hbound
  revert J M
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs L ht =>
      intro _ J M hK hb
      have hc : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g (CompanionIdeal.Construction.globalCompanionIdeal J M m b) (m * (b - m) - 1) = ⊤ := hK ▸ ht
      exact .terminal hb (CompanionIdeal.Construction.globalCompanionIdeal_terminal_residual_drop g J M m b hm hmb hb hc)
  | @blowup Y hY hN g L I hI hpos hp hs hbl tail ih =>
      intro hg J M hK hb
      let : Smooth g := hg
      let : Smooth (I.subschemeι ≫ g) := hs
      let π := GlobalBlowup.Data.Construction.globalBlowupToBase I hI
      let : Smooth (π ≫ g) := hbl
      obtain ⟨hJ, hM, _⟩ := CompanionIdeal.Construction.globalCompanionIdeal_smooth_center_permissible g I J M m b hm hmb (hK ▸ hp)
      have hnew : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI (m * (b - m)) =
          CompanionIdeal.Construction.globalCompanionIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)
            (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)) m b := by
        rw [hK]
        exact CompanionTransform.Construction.globalBlowup_companion_transform I J M hI m b hJ hM
      have hb' := OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound g I J hI m hJ hb
      exact .blowup hb I hI hM hJ hs hbl
        (ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m) (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)) hnew hb')

theorem CompanionSequence.Construction.exists_global_surface_companion_sequence
    (m b : ℕ) (hm : 0 < m) (hmb : m < b)
    (X : Scheme) [IsIntegral X] [CompactSpace X] (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [Smooth f]
    (J M : X.IdealSheafData) (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤)
    (hd : topologicalKrullDim X ≤ 2) : Nonempty (CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) := by
  let c := m * (b - m)
  have hc : 0 < c := Nat.mul_pos hm (by omega)
  have he : c - 1 + 1 = c := Nat.sub_add_cancel hc
  have hC := CompanionIdeal.Construction.globalCompanionIdeal_differential_bound f J M m b hmb hbound
  have hC' : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f (CompanionIdeal.Construction.globalCompanionIdeal J M m b) (c - 1 + 1) = ⊤ := by
    rw [he]
    exact hC
  have hex := GlobalSurface.BoundedSequence.Construction.exists_global_surface_fixed_control_sequence X f (CompanionIdeal.Construction.globalCompanionIdeal J M m b) (c - 1) hd hC'
  rw [he] at hex
  obtain ⟨T⟩ := hex
  exact ⟨T.toCompanion hm hmb J M rfl hbound⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Global
