import OAI.AlgebraicGeometry.Resolution.Blowups.Global.Companion
import OAI.AlgebraicGeometry.Resolution.Blowups.GlobalBoundary.SequenceCompatibility

/-! # Companion Compatibility -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups

noncomputable section

/-! Actual global companion phases retain integral centers and the full boundary compatibility of the resolving sequence. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

def Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence.integralCenters
    {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) : Prop :=
  match T with
  | @Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence.terminal _ _ _ _ _ _ _ _ _ => True
  | @Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence.blowup _ _ _ _ _ _ _ _ _ _ I _ _ _ _ _ tail => IsIntegral I.subscheme ∧ tail.integralCenters

def Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence.boundaryCompatible
    {m b : ℕ} {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} {M J : X.IdealSheafData}
    (T : Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J) :
    (β : Type) → [Fintype β] → (β → X.IdealSheafData) → Prop :=
  match T with
  | @Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence.terminal _ _ _ g _ _ _ _ _ => fun _ _ D => Nonempty (Global.MonomialBoundaryAtlas.Construction.GlobalMonomialBoundaryAtlas g D [Finset.univ])
  | @Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence.blowup _ _ _ _ _ g _ _ _ _ I hI _ _ _ _ tail => fun β _ D =>
      Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g I D) ∧
        tail.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D)

theorem Global.MonomialSequence.Construction.SmoothFixedControlSequence.exists_boundary_integral_companion
    {m b : ℕ} (hm : 0 < m) (hmb : m < b)
    {X : Scheme} {f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase} [Smooth f] {K : X.IdealSheafData}
    (T : Global.MonomialSequence.Construction.SmoothFixedControlSequence (m * (b - m)) X f K)
    (J M : X.IdealSheafData) (hK : K = Global.CompanionIdeal.Construction.globalCompanionIdeal J M m b)
    (hbound : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf f J m = ⊤) :
    ∀ (β : Type) [Fintype β] (D : β → X.IdealSheafData),
      T.integralCenters → T.boundaryCompatible β D →
      ∃ P : Global.CompanionSequence.Construction.SmoothGlobalCompanionSequence m b X f M J, P.integralCenters ∧ P.boundaryCompatible β D := by
  revert hK hbound J M
  revert ‹Smooth f›
  induction T with
  | @terminal Y g hs L ht =>
      intro _ J M hK hb β _ D _ hboundary
      have hc : Blowups.Smooth.DifferentialIdealSheaf.Construction.smoothDifferentialIdealSheaf g (Global.CompanionIdeal.Construction.globalCompanionIdeal J M m b) (m * (b - m) - 1) = ⊤ := hK ▸ ht
      refine ⟨.terminal hb (Global.CompanionIdeal.Construction.globalCompanionIdeal_terminal_residual_drop g J M m b hm hmb hb hc), ?_, ?_⟩
      · change True
        trivial
      · exact hboundary
  | @blowup Y hY hN g L I hI hpos hp hs hbl tail ih =>
      intro hg J M hK hb β _ D hcenters hboundary
      let : Smooth g := hg
      let : Smooth (I.subschemeι ≫ g) := hs
      let : Smooth (GlobalBlowup.Data.Construction.globalBlowupToBase I hI ≫ g) := hbl
      change IsIntegral I.subscheme ∧ tail.integralCenters at hcenters
      change Nonempty (Global.CanonicalBoundaryAtlas.Construction.GlobalMixedCenterAtlas g I D) ∧
        tail.boundaryCompatible (Option β) (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) at hboundary
      obtain ⟨hJ, hM, _⟩ := Global.CompanionIdeal.Construction.globalCompanionIdeal_smooth_center_permissible g I J M m b hm hmb (hK ▸ hp)
      have hnew : GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I L hI (m * (b - m)) =
          Global.CompanionIdeal.Construction.globalCompanionIdeal (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)
            (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)) m b := by
        rw [hK]
        exact Global.CompanionTransform.Construction.globalBlowup_companion_transform I J M hI m b hJ hM
      have hb' := Global.OrderBoundPreservation.Construction.globalBlowup_preserves_differential_order_bound g I J hI m hJ hb
      obtain ⟨P, hP, hPB⟩ := ih (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I J hI m)
        (GlobalControlled.Ideal.Construction.globalBlowupControlledIdeal I M hI (b - m)) hnew hb' (Option β)
        (CanonicalBoundaryTransform.Construction.globalBlowupCanonicalBoundary I hI D) hcenters.2 hboundary.2
      refine ⟨.blowup hb I hI hM hJ hs hbl P, ?_, ?_⟩
      · exact ⟨hcenters.1, hP⟩
      · exact ⟨hboundary.1, hPB⟩

end

end OAI.AlgebraicGeometry.Resolution.Blowups
